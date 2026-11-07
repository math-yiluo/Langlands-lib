import Langlands.Representation.Category.CoproductCompression
import Langlands.Representation.Category.ExactInclusion
import Langlands.CategoryTheory.Renard.GeneratorPresentation
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Compact compression on images of generator presentations -/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Langlands.LinearAlgebra.StableEndomorphism

namespace Langlands.SmoothRep

universe uG uV uI vC uC

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A common stable compression power passes to any actual smooth coproduct
vertex, with no bound on the index universe. -/
theorem compressedAction_stablePower_of_cofan
    {I : Type uI} [DecidableEq I]
    (A : I → SmoothRep.{0, uG, uV} ℂ G) (s : Cofan A) (hs : IsColimit s)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (b : ℕ)
    (hA : ∀ i, Stable (Jacquet.compressedAction
      (A i).representation (A i).isSmooth K hK g ^ b)) :
    Stable (Jacquet.compressedAction s.pt.representation s.pt.isSmooth K hK g ^ b) := by
  let e := cofanDirectSumEquiv A s hs
  have hsum : IsSmooth (Representation.directSum (fun i => (A i).representation)) :=
    Langlands.isSmooth_of_injective e.toIntertwiningMap e.injective s.pt.isSmooth
  exact Jacquet.compactCompressionStablePower_of_retract
    s.pt.representation (Representation.directSum (fun i => (A i).representation))
    s.pt.isSmooth hsum K hK g e.symm.toIntertwiningMap e.toIntertwiningMap
    (by ext x; exact e.apply_symm_apply x) b
    ((Jacquet.compressedAction_stablePower_directSum_iff
      (fun i => (A i).representation) (fun i => (A i).isSmooth)
      hsum K hK g b).mpr hA)

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  (T : C ⥤ SmoothRep.{0, uG, uV} ℂ G)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)

/-- One exponent gives a stable compact-compression power on every object
in the actual image of the supplied functor. -/
def FunctorCompressionStablePower (b : ℕ) : Prop :=
  ∀ M : C, Stable (Jacquet.compressedAction
    (T.obj M).representation (T.obj M).isSmooth K hK g ^ b)

/-- A right-exact functor preserving Hom-sized coproducts transfers a
generator's stable compression power to every object, with the same exponent. -/
theorem functorCompressionStablePower_of_generator
    [HasCoproducts.{vC} C] [T.Additive] [PreservesFiniteColimits T]
    (hcop : ∀ I : Type vC, PreservesColimitsOfShape (Discrete I) T)
    (P : C) (hP : Langlands.Renard.HomGenerator P) (b : ℕ)
    (hstable : Stable (Jacquet.compressedAction
      (T.obj P).representation (T.obj P).isSmooth K hK g ^ b)) :
    FunctorCompressionStablePower T K hK g b := by
  classical
  intro M
  obtain ⟨I, J, f, q, hz, hex, hepi⟩ :=
    Langlands.Renard.generatorPresentation P hP M
  have hsums (D : Type vC) :
      Stable (Jacquet.compressedAction
        (T.obj (∐ fun _ : D => P)).representation
        (T.obj (∐ fun _ : D => P)).isSmooth K hK g ^ b) := by
    let := hcop D
    exact compressedAction_stablePower_of_cofan
      (fun _ : D => T.obj P)
      (Cofan.mk _ (fun d => T.map (Sigma.ι (fun _ : D => P) d)))
      (isColimitCofanMkObjOfIsColimit T (fun _ : D => P)
        (Sigma.ι (fun _ : D => P)) (coproductIsCoproduct _))
      K hK g b (fun _ => hstable)
  have hright : ∀ S : ShortComplex C, S.Exact ∧ Epi S.g →
      (S.map T).Exact ∧ Epi (T.map S.g) :=
    ((Functor.preservesFiniteColimits_tfae T).out 4 2).mp
      (inferInstance : PreservesFiniteColimits T)
  obtain ⟨hT, hq⟩ := hright (ShortComplex.mk f q hz) ⟨hex, hepi⟩
  let := hq
  have hmodule := hT.map
    (toRep ⋙ forget₂ (Rep.{uV} ℂ G) (ModuleCat.{uV} ℂ))
  exact Jacquet.compressedAction_stablePower_of_rightExact
    (T.obj _).isSmooth (T.obj _).isSmooth (T.obj M).isSmooth K hK g
    (SmoothRep.hom (T.map f)) (SmoothRep.hom (T.map q))
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hmodule)
    ((SmoothRep.epi_iff_surjective _).mp hq) b (hsums J) (hsums I)

/-- Eventual stability on the generator image gives one positive stationary
threshold, chosen before every object in the image of the functor. -/
theorem functorCompressionStationary_of_generator
    [HasCoproducts.{vC} C] [T.Additive] [PreservesFiniteColimits T]
    (hcop : ∀ I : Type vC, PreservesColimitsOfShape (Discrete I) T)
    (P : C) (hP : Langlands.Renard.HomGenerator P)
    (hstable : EventuallyStable (Jacquet.compressedAction
      (T.obj P).representation (T.obj P).isSmooth K hK g)) :
    ∃ b : ℕ, 0 < b ∧ ∀ M : C, Jacquet.CompactCompressionStationaryFrom
      (T.obj M).representation (T.obj M).isSmooth K hK g b := by
  obtain ⟨b, hb, hpower⟩ := hstable
  refine ⟨b, hb, fun M => ?_⟩
  exact Jacquet.compactCompressionStationaryFrom_of_stablePower
    (T.obj M).representation (T.obj M).isSmooth K hK g hb
    (functorCompressionStablePower_of_generator T K hK g hcop P hP b hpower M)

end Langlands.SmoothRep
