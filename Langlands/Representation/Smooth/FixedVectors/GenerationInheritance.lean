import Langlands.Representation.Smooth.FixedVectors.GenerationInheritanceStatement
import Langlands.Representation.Smooth.FixedVectors.FiniteTypes
import Langlands.Representation.Classification.SupercuspidalSupport
import Mathlib.RepresentationTheory.Semisimple

noncomputable section

namespace Langlands

open scoped MonoidAlgebra

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [Field R] [Group G] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- Semisimplicity and generation by fixed vectors pass through a surjective
intertwiner. Surjectivity on fixed vectors is not assumed or used in this proof. -/
theorem semisimple_fixedVectors_generate_of_surjective
    {ρ : Representation R G V} {σ : Representation R G W}
    (K : Subgroup G) (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (hρ : Representation.IsSemisimpleRepresentation ρ)
    (hgen : ∀ S : Subrepresentation ρ, fixedVectors ρ K ≤ S.toSubmodule → S = ⊤) :
    Representation.IsSemisimpleRepresentation σ ∧
      ∀ S : Subrepresentation σ, fixedVectors σ K ≤ S.toSubmodule → S = ⊤ := by
  let : IsSemisimpleModule R[G] ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hρ
  constructor
  · apply (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mpr
    exact IsSemisimpleModule.of_surjective
      (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf
  · intro S hS
    let T : Subrepresentation ρ :=
      { toSubmodule := S.toSubmodule.comap f.toLinearMap
        apply_mem_toSubmodule := by
          intro g v hv
          change f (ρ g v) ∈ S
          rw [f.isIntertwining]
          exact S.apply_mem_toSubmodule g hv }
    have hT : T = ⊤ := hgen T (fun v hv => hS (map_mem_fixedVectors f hv))
    apply top_unique
    intro w _
    obtain ⟨v, rfl⟩ := hf w
    have hv : v ∈ T := by rw [hT]; trivial
    exact hv

/-- In a semisimple ambient representation, an injection splits equivariantly,
so generation by fixed vectors passes to its source. -/
theorem semisimple_fixedVectors_generate_of_injective
    {ρ : Representation R G V} {σ : Representation R G W}
    (K : Subgroup G) (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (hσ : Representation.IsSemisimpleRepresentation σ)
    (hgen : ∀ S : Subrepresentation σ, fixedVectors σ K ≤ S.toSubmodule → S = ⊤) :
    Representation.IsSemisimpleRepresentation ρ ∧
      ∀ S : Subrepresentation ρ, fixedVectors ρ K ≤ S.toSubmodule → S = ⊤ := by
  let : IsSemisimpleModule R[G] σ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp hσ
  let j := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property j hf
    (LinearMap.id : ρ.asModule →ₗ[R[G]] ρ.asModule)
  have hr' : Function.LeftInverse r j := fun x =>
    congrArg (fun t : ρ.asModule →ₗ[R[G]] ρ.asModule => t x) hr
  let g := (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ).symm r
  exact semisimple_fixedVectors_generate_of_surjective K g hr'.surjective hσ hgen

namespace SmoothRep

open CategoryTheory

variable [TopologicalSpace G]

/-- A fixed compact-open choice can be retained throughout the constituent
induction: semisimplicity and fixed-vector generation over H pass to every
actual G-subquotient. Compactness and openness are unnecessary for this step. -/
theorem semisimple_fixedVectors_generate_subquotient
    {A B : SmoothRep.{uR, uG, uV} R G} (H K : Subgroup G) (hKH : K ≤ H)
    (hA : Representation.IsSemisimpleRepresentation (A.representation.comp H.subtype))
    (hgen : ∀ S : Subrepresentation (A.representation.comp H.subtype),
      fixedVectors A.representation K ≤ S.toSubmodule → S = ⊤)
    (h : IsSubquotient B A) :
    Representation.IsSemisimpleRepresentation (B.representation.comp H.subtype) ∧
      ∀ S : Subrepresentation (B.representation.comp H.subtype),
        fixedVectors B.representation K ≤ S.toSubmodule → S = ⊤ := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  let iH : Representation.IntertwiningMap (C.representation.comp H.subtype)
      (A.representation.comp H.subtype) :=
    { toLinearMap := (hom i).toLinearMap
      isIntertwining' g := (hom i).isIntertwining' g }
  let qH : Representation.IntertwiningMap (C.representation.comp H.subtype)
      (B.representation.comp H.subtype) :=
    { toLinearMap := (hom q).toLinearMap
      isIntertwining' g := (hom q).isIntertwining' g }
  have hgenA : ∀ S : Subrepresentation (A.representation.comp H.subtype),
      fixedVectors (A.representation.comp H.subtype) (K.comap H.subtype) ≤ S.toSubmodule →
      S = ⊤ := by
    simpa only [fixedVectors_comp_subtype A.representation H K hKH] using hgen
  obtain ⟨hC, hgenC⟩ := semisimple_fixedVectors_generate_of_injective
    (K.comap H.subtype) iH hi hA hgenA
  have hB := semisimple_fixedVectors_generate_of_surjective
    (K.comap H.subtype) qH hq hC hgenC
  simpa only [fixedVectors_comp_subtype B.representation H K hKH] using hB

end SmoothRep

/-- The complete inheritance bundle, with independent coefficient, group,
source-carrier and target-carrier universes. -/
theorem semisimpleFixedVectorsGenerationInheritance :
    SemisimpleFixedVectorsGenerationInheritanceStatement.{uR, uG, uV, uW} := by
  refine ⟨?_, ?_, ?_⟩
  · intro R _ G _ V _ _ W _ _ ρ σ K f hf hρ hgen
    exact semisimple_fixedVectors_generate_of_surjective K f hf hρ hgen
  · intro R _ G _ V _ _ W _ _ ρ σ K f hf hσ hgen
    exact semisimple_fixedVectors_generate_of_injective K f hf hσ hgen
  · intro R _ G _ _ A B H K hKH hA hgen h
    exact SmoothRep.semisimple_fixedVectors_generate_subquotient H K hKH hA hgen h

end Langlands
