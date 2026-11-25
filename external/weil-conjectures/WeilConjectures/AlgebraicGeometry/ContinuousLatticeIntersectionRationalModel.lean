/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersection
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitModel
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeKernelModel

/-! # Rational kernel models of the finite-sheet lattice intersection -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- On compact covering schemes the canonical intersection has a rational
finite-matrix kernel presentation.
Source: Bhatt--Scholze, Lemma 6.8.13; the intersection argument is an agent variant.
(auxiliary; not a blueprint node)

Proof. Take the split-cover model. The integral localization unit is monic on
its standard finite free module, so the image-pullback is the intersection of two
subobjects. In an abelian category this intersection is the kernel of the second
subobject's map to the first quotient. Restriction of scalars preserves cokernels;
transport this quotient along the supplied rational finite free cokernel basis.
The resulting kernel map is exactly the integral adjoint of the rational quotient
projection. That projection is epi, being a cokernel map followed by an isomorphism.
All maps are canonical categorical maps; no denominator clearing is used here. -/
theorem continuousLatticeIntersection_rationalModel
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P)
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) U))
    (hM : IsLocallyFree (condensedRingObj (integralCoeff ℓ E) U) M)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      CompactSpace (C.X s) ∧
      let R := condensedRingObj (integralCoeff ℓ E) (C.X s)
      let T := (ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (C.f s)))
      let F := Mod.extendScalars
        (coefficientMap (integralScalarMap ℓ E) (C.X s))
      ∃ (n m : ℕ) (f : F.obj (Mod.finiteFree R n) ⟶ F.obj (Mod.finiteFree R m)),
        Epi f ∧ Nonempty
          (T.obj (latticeIntersection (integralScalarMap ℓ E) X P p M e) ≅
            kernel ((Mod.extendRestrictAdjunction
              (coefficientMap (integralScalarMap ℓ E) (C.X s))).homEquiv _ _ f)) := by
  classical
  obtain ⟨C, hC⟩ := continuousLatticeIntersection_splitModel ℓ E X P hP p M hM e
  refine ⟨C, fun s ↦ ?_⟩
  obtain ⟨hs, r, n, m, i, hi, ⟨ec⟩, ⟨eN⟩⟩ := hC s
  refine ⟨hs, n, m, ?_⟩
  let φ := coefficientMap (integralScalarMap ℓ E) (C.X s)
  let F := Mod.extendScalars φ
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology (C.X s)) Ab.{u + 1}) φ
  let adj := Mod.extendRestrictAdjunction φ
  let D := Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) (C.X s)) n
  let q := cokernel.π i ≫ ec.hom
  have : Mono i := hi
  have : Mono (adj.unit.app D) := integralFiniteFree_unit_mono ℓ E (C.X s) n
  let d := (PreservesCokernel.iso G i).symm ≪≫ G.mapIso ec
  have hd : cokernel.π (G.map i) ≫ d.hom = G.map q := by
    dsimp only [d, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, q]
    rw [← Category.assoc, PreservesCokernel.iso_inv, π_comp_cokernelComparison,
      ← G.map_comp]
  have hb : (adj.unit.app D ≫ cokernel.π (G.map i)) ≫ d.hom =
      adj.homEquiv D _ q := by
    rw [Category.assoc, hd]
    rfl
  refine ⟨q, inferInstance, ⟨eN ≪≫ imagePullbackIsoKernel (G.map i) (adj.unit.app D) ≪≫
    (kernelCompMono (adj.unit.app D ≫ cokernel.π (G.map i)) d.hom).symm ≪≫
      kernelIsoOfEq hb⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
