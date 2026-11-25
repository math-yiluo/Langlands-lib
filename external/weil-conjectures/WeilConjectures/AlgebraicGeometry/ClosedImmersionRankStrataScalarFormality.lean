/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionRankStrataScalarHomologyLift
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSumsCofan
import WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSumsHomology

/-! # Scalar formality on the rank strata of a closed subscheme

Source: Stacks Project, Tag 0BQZ, single-degree truncation and reconstruction;
the rank-stratum assembly in lem-sc-koszul-regular-immersion-derived-hom, step 3
(blueprint: lem-sc-closed-immersion-rank-strata-scalar-formality).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

private theorem coprojection_isIso_of_other_zero
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    {I : Type*} (A : I → C) [HasCoproduct A]
    (n : I) (h : ∀ m, m ≠ n → IsZero (A m)) : IsIso (Sigma.ι A n) := by
  classical
  let p : ∐ A ⟶ A n := Sigma.desc (fun m ↦ if e : m = n then eqToHom (congrArg A e)
    else 0)
  refine ⟨⟨p, ?_, ?_⟩⟩
  · simp [p]
  · apply Sigma.hom_ext
    intro m
    by_cases e : m = n
    · subst m
      simp [p]
    · exact (h m e).eq_of_src _ _

private theorem inclusion_homology_isIso
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : CochainComplex C ℤ) (hd : ∀ a b, P.d a b = 0) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C n).map
      (DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle (𝟙 (P.X n))
        (fun b _ ↦ by rw [hd, comp_zero])))) := by
  let j := HomologicalComplex.mkHomFromSingle (𝟙 (P.X n))
    (fun b _ ↦ by rw [hd, comp_zero])
  have hj : IsIso (j.f n) := by
    dsimp [j]
    rw [HomologicalComplex.mkHomFromSingle_f, Category.comp_id]
    infer_instance
  let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map j
  let γ := ShortComplex.LeftHomologyMapData.ofZeros φ
    (by simp [HomologicalComplex.single]) (by simp [HomologicalComplex.single])
    (hd _ _) (hd _ _)
  have : ShortComplex.QuasiIso φ := γ.quasiIso_iff.mpr (by
    change IsIso (j.f n)
    exact hj)
  have : IsIso (HomologicalComplex.homologyMap j n) := by
    change IsIso (ShortComplex.homologyMap φ)
    infer_instance
  exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C n) j).mpr this

private theorem zeroDifferentialAssembly (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hd : ∀ a b, P.d a b = 0)
    (K : schemeDerivedCategory Y)
    (hlift : ∀ n, ∃ f : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj (P.X n) ⟶ K,
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).map f)) :
    Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  classical
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  have : HasColimitsOfShape (Discrete (ULift.{u} ℤ)) C := inferInstance
  have : HasColimitsOfShape (Discrete (ULift.{u} ℤ)) (CochainComplex C ℤ) := by
    refine ⟨fun F ↦ ?_⟩
    have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
      HasColimitsOfShape.has_colimit _
    exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩
  let L (n : ULift.{u} ℤ) : CochainComplex C ℤ :=
    (HomologicalComplex.single C (ComplexShape.up ℤ) n.down).obj (P.X n.down)
  let j (n : ULift.{u} ℤ) : L n ⟶ P := HomologicalComplex.mkHomFromSingle (𝟙 (P.X n.down))
    (fun b _ ↦ by rw [hd, comp_zero])
  let f (n : ULift.{u} ℤ) : DerivedCategory.Q.obj (L n) ⟶ K := (hlift n.down).choose
  have hf (n : ℤ) : IsIso ((DerivedCategory.homologyFunctor C n).map (f ⟨n⟩)) :=
    (hlift n).choose_spec
  let D := DerivedCategory.Q.obj (∐ L)
  obtain ⟨hc⟩ := derivedAmbientDirectSumsCofan Y (ULift.{u} ℤ)
    (fun n ↦ DerivedCategory.Q.obj (L n)) L (fun _ ↦ Iso.refl _)
  let g : D ⟶ K := hc.desc (Cofan.mk K f)
  let a : D ⟶ DerivedCategory.Q.obj P := DerivedCategory.Q.map (Sigma.desc j)
  have hi (n : ℤ) : IsIso ((DerivedCategory.homologyFunctor C n).map
      (DerivedCategory.Q.map (Sigma.ι L ⟨n⟩))) := by
    let H := DerivedCategory.homologyFunctor C n
    have hzero (m : ULift.{u} ℤ) (hm : m ≠ ⟨n⟩) : IsZero (H.obj (DerivedCategory.Q.obj (L m))) :=
      (HomologicalComplex.isZero_single_obj_homology
        (ComplexShape.up ℤ) m.down (P.X m.down) n (by
          intro e
          apply hm
          exact ULift.ext e.symm)).of_iso
          ((DerivedCategory.homologyFunctorFactors C n).app (L m))
    have := coprojection_isIso_of_other_zero
      (fun m ↦ H.obj (DerivedCategory.Q.obj (L m))) ⟨n⟩ hzero
    have hsum : IsIso (Sigma.desc
        (fun m ↦ H.map (DerivedCategory.Q.map (Sigma.ι L m)))) := by
      simpa only [Iso.refl_inv, Category.id_comp] using
        derivedAmbientDirectSumsHomology Y (ULift.{u} ℤ)
          (fun m ↦ DerivedCategory.Q.obj (L m)) L (fun _ ↦ Iso.refl _) n
    have he : H.map (DerivedCategory.Q.map (Sigma.ι L ⟨n⟩)) =
        Sigma.ι (fun m ↦ H.obj (DerivedCategory.Q.obj (L m))) ⟨n⟩ ≫
          Sigma.desc (fun m ↦ H.map (DerivedCategory.Q.map (Sigma.ι L m))) := by simp
    rw [he]
    infer_instance
  have ha : IsIso a := (DerivedCategory.isIso_iff C a).mpr (by
    intro n
    have he : DerivedCategory.Q.map (Sigma.ι L ⟨n⟩) ≫ a = DerivedCategory.Q.map (j ⟨n⟩) := by
      simp [a, ← Functor.map_comp]
    have := hi n
    have := inclusion_homology_isIso P hd n
    have hiso : IsIso ((DerivedCategory.homologyFunctor C n).map
        (DerivedCategory.Q.map (Sigma.ι L ⟨n⟩)) ≫
          (DerivedCategory.homologyFunctor C n).map a) := by
      rwa [← Functor.map_comp, he]
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map (Sigma.ι L ⟨n⟩)))
      ((DerivedCategory.homologyFunctor C n).map a))
  have hg : IsIso g := (DerivedCategory.isIso_iff C g).mpr (by
    intro n
    have he : DerivedCategory.Q.map (Sigma.ι L ⟨n⟩) ≫ g = f ⟨n⟩ := by
      simpa [g] using hc.fac (Cofan.mk K f) ⟨⟨n⟩⟩
    have := hi n
    have := hf n
    have hiso : IsIso ((DerivedCategory.homologyFunctor C n).map
        (DerivedCategory.Q.map (Sigma.ι L ⟨n⟩)) ≫
          (DerivedCategory.homologyFunctor C n).map g) := by
      rwa [← Functor.map_comp, he]
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map (Sigma.ι L ⟨n⟩)))
      ((DerivedCategory.homologyFunctor C n).map g))
  exact ⟨(asIso a).symm ≪≫ asIso g⟩

/-- A family of arbitrary module sheaves on disjoint rank strata is formal after
scalar direct image along a closed immersion. The family need not be finite.

Source: Stacks Project, Tag 0BQZ, single-degree truncation; parent reconstruction
step 3 (blueprint: lem-sc-closed-immersion-rank-strata-scalar-formality).

Proof:
1. Put Z_n = {z | r z = n}. Each Z_n is clopen in Z. Its image and the image of
   its complement are closed in Y, since i is a closed immersion. Put
   V_n = Y minus i(Z minus Z_n), and V_out = Y minus i(Z). These opens cover Y.
   For distinct m,n, V_m intersect V_n is contained in V_out. On V_n only T^n
   can be nonzero after direct image; on V_out every pushed-forward T^q is zero.
   In particular the family of closed supports i(Z_n) is locally finite in Y.
2. Exact restriction to V_n and hK show that K restricted to V_n has cohomology
   only in degree n, identified with the restricted direct image of E_n. Choose
   a representative and truncate above and below n. The truncation maps are
   quasi-isomorphisms, and identify this restriction with that sheaf in degree n.
   The restricted zero-differential complex has exactly the same single term.
3. Extend each local identification by zero from V_n to Y. Extension by zero
   for module sheaves is exact. The counit maps from the coproduct of these
   extended restrictions to K are isomorphisms on cohomology: at a point of i(Z)
   exactly one rank support contributes, and outside i(Z) all cohomology is zero.
   Coproducts of module sheaves are exact, so these counits are isomorphisms in
   the derived category. Apply the same construction to the zero-differential
   comparison complex. Direct sum of the extended single-degree isomorphisms,
   followed by the two counit isomorphisms, gives the claimed isomorphism.
There is no need to glue arbitrary derived isomorphisms. The rank supports are
closed in Y, not asserted to be open in Y. Empty Z gives zero; rank zero is the
ordinary degree-zero case. Unbounded rank is allowed by the coproduct argument.
Neither algebra-module structure on K nor a derived category on Z is needed. -/
theorem closedImmersion_rankStrata_scalar_formality
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (r : LocallyConstant Z ℕ)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (hK : ∀ n : ℤ, Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj K ≅
        (Scheme.Modules.pushforward i).obj (T n))) :
    Nonempty (K ≅ DerivedCategory.Q.obj
      (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.of T (fun _ => 0) (fun _ => zero_comp)))) := by
  classical
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let F := Scheme.Modules.pushforward i
  let P := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (CochainComplex.of T (fun _ ↦ 0) (fun _ ↦ zero_comp))
  obtain ⟨e⟩ := zeroDifferentialAssembly Y P
    (fun a b ↦ by
      simp only [P, Functor.mapHomologicalComplex_obj_d, CochainComplex.of.d,
        zero_comp, dite_eq_ite, ite_self]
      exact Functor.map_zero F _ _) K (fun n ↦ by
      obtain ⟨f, hf⟩ := closedImmersion_rankStrata_scalar_homology_lift
        i r E T hT K n (fun m _ ↦ hK m) (hK n).some.inv
      refine ⟨f, ?_⟩
      have hiso : IsIso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso C n).inv.app (F.obj (T n)) ≫
            (DerivedCategory.homologyFunctor C n).map f) := by
        rw [hf]
        infer_instance
      exact IsIso.of_isIso_comp_left
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso C n).inv.app (F.obj (T n)))
        ((DerivedCategory.homologyFunctor C n).map f))
  exact ⟨e.symm⟩

end AlgebraicGeometry
