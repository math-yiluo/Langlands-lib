/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicGlobalDerivedHom
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.Adic.AdicDerivedGlobalSectionsCoproducts
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleInternalHomLowerBound
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.StratifiedPerfectInternalHomCoproducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Integral constructible complexes and uniformly bounded below sums

Coproducts are supplied as colimit cofans, so the statement is independent of
chosen coproduct objects. Their universal property constructs exactly the comparison
induced by the individual coprojections. The empty family is included.

## References

* Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.12 and Proposition 6.8.11(3)
* Bhatt--Scholze, Lemma 6.8.12, using Proposition 6.8.11(3)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Global derived Hom out of an integral constructible complex commutes with sums
of complexes having one common integer cohomological lower bound. The map is the
unique map whose component at i is RHom(K,-) of the ith coprojection. Both sums are
coproducts in the ambient derived categories, with no completion of their sum. -/
theorem integralConstructible_boundedBelow_compactness
    (T : Scheme.{u}) [IsNoetherian T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (hdim : ∃ N : ℕ, topologicalKrullDim T ≤ (N : WithBot ℕ∞))
    (hℓ : ∀ x : T, IsUnit (ℓ : T.presheaf.stalk x))
    (K : PbcIntegralCategory ℓ E T hdim hℓ)
    (I : Type (u + 1))
    (M : I → DerivedCategory (pbcModules T
      (pbcAdicCompletion T (pbcIntegralDatum ℓ E))))
    (_hM : ∃ n : ℤ, ∀ i : I, DerivedCategory.IsGE (M i) n)
    (s : Cofan M) (_hs : IsColimit s)
    (t : Cofan (fun i : I ↦
      (adicGlobalRHom T (pbcIntegralDatum ℓ E) K.obj).obj (M i)))
    (ht : IsColimit t) :
    IsIso (ht.desc (Cofan.mk
      ((adicGlobalRHom T (pbcIntegralDatum ℓ E) K.obj).obj s.pt)
      (fun i : I ↦ (adicGlobalRHom T (pbcIntegralDatum ℓ E) K.obj).map
        (s.inj i)))) := by
  obtain ⟨N, hN⟩ := _hM
  have hℓ' : IsUnit (ℓ : Γ(T, ⊤)) := by
    apply T.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using hℓ x
  have hchar := integralStratifiedPerfectCharacterization T ℓ E hdim hℓ' K.obj
  have hperf := hchar.1.mp K.property
  obtain ⟨a, b, _, _, hb⟩ := (hchar.2.mp hperf).1
  have : K.obj.IsLE b := hb
  let H := (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u + 1}
    (ProEt.topology T) (pbcAdicCompletion T (pbcIntegralDatum ℓ E)))).obj (Opposite.op K.obj)
  let G := adicDerivedGlobalSections T (pbcIntegralDatum ℓ E)
  have : PreservesColimit (Discrete.functor M) H :=
    integralStratifiedPerfect_internalHom_preservesColimit
      T (pbcIntegralDatum ℓ E) K.obj b hperf I M N hN
  have hbound (i : I) : (H.obj (M i)).IsGE (N - b) := by
    have : (M i).IsGE N := hN i
    exact proEtale_internalHom_isGE T (pbcAdicCompletion T (pbcIntegralDatum ℓ E))
      K.obj (M i) b N
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (PbcIntegralRing ℓ E)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  have : PreservesColimit (Discrete.functor (fun i ↦ H.obj (M i))) G :=
    proEtale_derivedGlobalSections_boundedBelow_preservesColimit T
      (pbcAdicCompletion T (pbcIntegralDatum ℓ E))
      (adicScalar T (pbcIntegralDatum ℓ E) (Opposite.op (⊤_ T.ProEt)))
      I (fun i ↦ H.obj (M i)) (N - b) hbound
  have hsH : IsColimit (Cofan.mk (H.obj s.pt) (fun i ↦ H.map (s.inj i))) :=
    (isColimitMapCoconeCofanMkEquiv H M s.inj).1 (isColimitOfPreserves H _hs)
  have hc : IsColimit (Cofan.mk (G.obj (H.obj s.pt))
      (fun i ↦ G.map (H.map (s.inj i)))) :=
    (isColimitMapCoconeCofanMkEquiv G (fun i ↦ H.obj (M i))
      (fun i ↦ H.map (s.inj i))).1 (isColimitOfPreserves G hsH)
  exact (ht.nonempty_isColimit_iff_isIso_desc).mp ⟨hc⟩

end AlgebraicGeometry.Scheme
