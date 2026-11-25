/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulQuotientCoefficientComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.AffineKoszulHomCoefficientComplexSquare
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Homology transport for the finite free Koszul coefficient square

Source: Stacks Project, Tags 0BQZ and 01HV. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem homology_coefficient_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (P Q : CochainComplex C ℕ) (X Y : CochainComplex D ℤ)
    (q : P ⟶ Q) (a : X ⟶ Y) (m : ℕ)
    (eX : X ≅ (F.mapHomologicalComplex (.up ℤ)).obj
      (P.extend ComplexShape.embeddingUpNat))
    (eY : Y ≅ (F.mapHomologicalComplex (.up ℤ)).obj
      (Q.extend ComplexShape.embeddingUpNat))
    (hs : a ≫ eY.hom = eX.hom ≫ (F.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap q ComplexShape.embeddingUpNat)) :
    ∃ (bX : X.homology (m : ℤ) ≅ F.obj (P.homology m))
      (bY : Y.homology (m : ℤ) ≅ F.obj (Q.homology m)),
      HomologicalComplex.homologyMap a (m : ℤ) ≫ bY.hom =
        bX.hom ≫ F.map (HomologicalComplex.homologyMap q m) := by
  let H := HomologicalComplex.homologyFunctor D (.up ℤ) (m : ℤ)
  let μ := F.mapHomologicalComplexHomologyIso (.up ℤ) (m : ℤ)
  let Pe := P.extend ComplexShape.embeddingUpNat
  let Qe := Q.extend ComplexShape.embeddingUpNat
  let qe := HomologicalComplex.extendMap q ComplexShape.embeddingUpNat
  let εP := P.extendHomologyIso ComplexShape.embeddingUpNat (j := m) rfl
  let εQ := Q.extendHomologyIso ComplexShape.embeddingUpNat (j := m) rfl
  refine ⟨H.mapIso eX ≪≫ μ.app Pe ≪≫ F.mapIso εP,
    H.mapIso eY ≪≫ μ.app Qe ≪≫ F.mapIso εQ, ?_⟩
  have h₁ : CommSq (H.map a) (H.map eX.hom) (H.map eY.hom)
      (H.map ((F.mapHomologicalComplex (.up ℤ)).map qe)) :=
    ⟨(H.map_comp _ _).symm.trans
      ((congrArg (fun t ↦ H.map t) hs).trans (H.map_comp _ _))⟩
  have h₂ : CommSq (H.map ((F.mapHomologicalComplex (.up ℤ)).map qe))
      (μ.app Pe).hom (μ.app Qe).hom
      (F.map (HomologicalComplex.homologyMap qe (m : ℤ))) := ⟨μ.hom.naturality qe⟩
  have he := congrArg (fun t ↦ F.map t)
    (HomologicalComplex.extendHomologyIso_hom_naturality q
      ComplexShape.embeddingUpNat (j := m) rfl)
  simp only [Functor.map_comp] at he
  have h₃ : CommSq (F.map (HomologicalComplex.homologyMap qe (m : ℤ)))
      (F.map εP.hom) (F.map εQ.hom)
      (F.map (HomologicalComplex.homologyMap q m)) := ⟨he⟩
  simpa only [H, HomologicalComplex.homologyFunctor, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc] using
    (h₁.vert_comp h₂ |>.vert_comp h₃).w


/-- The finite free coefficient square remains commutative on homology.
Source: Stacks Project, Tag 0BQZ, displayed Hom coefficient square;
Tag 01HV, exact associated sheafification.
(blueprint: lem-sc-affine-koszul-hom-coefficient-homology-square).

Proof: Apply the homology functor to the finite free complex coefficient square.
The exact tilde and chart transport functors identify the homology of the
mapped complex with the mapped homology. This comparison is natural in the
coefficient reduction morphism. The natural extension homology isomorphisms
then identify the integer-degree m homology with the natural-degree m homology.
Compose the three commuting squares. No closed immersion or coefficient
adjunction map is involved. -/
theorem affine_koszul_hom_coefficient_homology_square
    {Y : Scheme.{u}} (U : Y.affineOpens) (I : Ideal (Γ(Y, U.1)))
    (n m : ℕ) (f : Fin n → Γ(Y, U.1))
    (H : CochainComplex (SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ℤ ⥤
      CochainComplex (SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ℤ)
    (hH : H =
      let A := (Γ(Y, U.1) : Type u)
      let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
      let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A n f).extend ComplexShape.embeddingDownNat)
      (homComplexFunctor (R := U.1.toScheme.toRingedSpace.sheaf)).obj (op E)) :
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let S := CochainComplex.singleFunctor U.1.toScheme.Modules 0
    let D := HomologicalComplex.homologyFunctor U.1.toScheme.Modules
      (ComplexShape.up ℤ) (m : ℤ)
    let G := S ⋙ H ⋙ D
    ∃ (cO : G.obj (T.obj (ModuleCat.of A A)) ≅
        T.obj ((ExteriorAlgebra.koszulDualComplex A n f).homology m))
      (cQ : G.obj (T.obj (ModuleCat.of A (A ⧸ I))) ≅
        T.obj ((ExteriorAlgebra.koszulQuotientDualComplex A I n f).homology m)),
      G.map (T.map (ModuleCat.ofHom I.mkQ)) ≫ cQ.hom = cO.hom ≫ T.map
        (HomologicalComplex.homologyMap
          (ExteriorAlgebra.koszulCoefficientReduction A I n f) m) := by
  let A := (Γ(Y, U.1) : Type u)
  let T₀ := tilde.functor Γ(Y, U.1)
  let V := Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let T := T₀ ⋙ V
  let : PreservesFiniteLimits T₀ := tilde_preserves_finite_limits A
  let : PreservesFiniteLimits V := by dsimp [V]; infer_instance
  let : PreservesFiniteColimits V := by dsimp [V]; infer_instance
  let : PreservesFiniteLimits T := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits T := comp_preservesFiniteColimits _ _
  obtain ⟨cO, cQ, hc⟩ := affine_koszul_hom_coefficient_complex_square U I n f H hH
  exact homology_coefficient_square T
    (ExteriorAlgebra.koszulDualComplex A n f)
    (ExteriorAlgebra.koszulQuotientDualComplex A I n f) _ _
    (ExteriorAlgebra.koszulCoefficientReduction A I n f)
    (H.map ((CochainComplex.singleFunctor U.1.toScheme.Modules 0).map
      (T.map (ModuleCat.ofHom I.mkQ)))) m cO cQ hc

end AlgebraicGeometry
