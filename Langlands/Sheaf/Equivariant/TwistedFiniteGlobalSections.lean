import Langlands.Sheaf.Equivariant.TwistedOver
import Langlands.Sheaf.Equivariant.LocalActionDiscretePart

/-!
# Finite-cover descent of discreteness at the twisted base

A locally discrete module sheaf has discrete sections at the base of a twisted
site if every covering sieve of the base contains a finite covering family.
All arrows from lifted local actions to the base are locally equivariant:
the twist of the arrow conjugates the relevant open fixing subgroup.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory Opposite

universe w v u uG

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable [P.ContainsIdentities]

/-- An arrow to the twisted base is determined by its twist. -/
theorem hom_to_base_ext {U : TwistedOver P ρ} {f f' : U ⟶ base P ρ}
    (h : Hom.twist f = Hom.twist f') : f = f' := by
  apply hom_ext h
  have hf := Hom.w f
  have hf' := Hom.w f'
  change Hom.left f ≫ 𝟙 X = _ at hf
  change Hom.left f' ≫ 𝟙 X = _ at hf'
  erw [Category.comp_id] at hf hf'
  rw [h] at hf
  exact hf.trans hf'.symm

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Any arrow from a lifted local action to the base is locally equivariant
for the canonical base action. -/
theorem isLocallyEquivariant_to_base {U : TwistedOver P ρ} {H : OpenSubgroup G}
    {b : (H : Subgroup G) →* (End U)ᵐᵒᵖ} (hb : IsLift b) (f : U ⟶ base P ρ) :
    IsLocallyEquivariant
      ((baseAction P ρ).comp (⊤ : OpenSubgroup G).toSubgroup.subtype) b f := by
  intro K hKH
  let c : G →* G := (MulAut.conj (Hom.twist f)⁻¹).toMonoidHom
  have hc : Continuous c := IsTopologicalGroup.continuous_conj _
  refine ⟨K.comap c hc, le_top, fun h hh => ?_⟩
  let k : (H : Subgroup G) := ⟨c h, hKH hh⟩
  refine ⟨k, hh, hom_to_base_ext ?_⟩
  rw [comp_twist, comp_twist, hb k]
  change Hom.twist f * (k : G)⁻¹ = (h : G)⁻¹ * Hom.twist f
  simp [k, c, mul_assoc]

/-- Every covering sieve of the twisted base contains a finite family whose
generated sieve still covers the base. -/
def HasFiniteBaseSubcovers (J : GrothendieckTopology (TwistedOver P ρ)) : Prop :=
  ∀ (S : Sieve (base P ρ)), S ∈ J (base P ρ) →
    ∃ (n : ℕ) (V : Fin n → TwistedOver P ρ) (f : ∀ i, V i ⟶ base P ρ),
      (∀ i, S (f i)) ∧ Sieve.ofArrows V f ∈ J (base P ρ)

variable {R : Type w} [CommRing R]

/-- If the discrete sieve of a section at the base covers, finite base
subcovers and a system of lifted local actions make the section discrete. -/
theorem isDiscreteSection_base_of_discreteSieve_mem
    {J : GrothendieckTopology (TwistedOver P ρ)} (hfin : HasFiniteBaseSubcovers J)
    (L : LocalActionSystem (TwistedOver P ρ) G) (hL : L.IsLiftSystem)
    {F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R} (hF : Presheaf.IsSheaf J F)
    (s : F.obj (op (base P ρ))) (hs : L.discreteSieve F s ∈ J (base P ρ)) :
    IsDiscreteSection F
      ((baseAction P ρ).comp (⊤ : OpenSubgroup G).toSubgroup.subtype) s := by
  obtain ⟨n, V, f, hf, hcov⟩ := hfin _ hs
  choose W k p H b hb hdisc hfac using hf
  have hle : Sieve.ofArrows V f ≤ Sieve.ofArrows W p := by
    rintro Z _ ⟨Y, l, _, ⟨i⟩, rfl⟩
    refine ⟨W i, l ≫ k i, p i, ⟨i⟩, ?_⟩
    rw [Category.assoc, hfac i]
  have hcov' := J.superset_covering hle hcov
  refine IsDiscreteSection.of_finite_family
    (fun i => isLocallyEquivariant_to_base (hL _ _ _ (hb i)) (p i)) hdisc ?_
  intro t t' htt'
  refine isSeparated_of_isSheaf hF hcov' ?_
  rintro Z _ ⟨Y, l, _, ⟨i⟩, rfl⟩
  rw [op_comp, F.map_comp, CategoryTheory.comp_apply, CategoryTheory.comp_apply, htt' i]

/-- Under finite base subcovers, every global section of a locally discrete
module sheaf is discrete for the canonical action at the base. -/
theorem isDiscreteSection_base_of_locallyDiscrete
    {J : GrothendieckTopology (TwistedOver P ρ)} (hfin : HasFiniteBaseSubcovers J)
    (L : LocalActionSystem (TwistedOver P ρ) G) (hL : L.IsLiftSystem)
    {F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R} (hF : Presheaf.IsSheaf J F)
    (hloc : L.IsLocallyDiscrete J F) (s : F.obj (op (base P ρ))) :
    IsDiscreteSection F
      ((baseAction P ρ).comp (⊤ : OpenSubgroup G).toSubgroup.subtype) s :=
  isDiscreteSection_base_of_discreteSieve_mem hfin L hL hF s (hloc _ s)

end Langlands.Sheaf.Equivariant.TwistedOver
