import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Neighborhood

/-! # Extension of complex characters from open subgroups -/

noncomputable section

universe u v

namespace Langlands.Topology

/-- The additive version of the group of complex units is divisible by naturals. -/
@[instance_reducible]
def complexUnitsDivisibleByNat : DivisibleBy (Additive ℂˣ) ℕ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn a ↦ by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      intro h
      have : (a.toMul : ℂ) = 0 := by simpa [h, hn] using hz.symm
      exact a.toMul.ne_zero this
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    change Units.mk0 z hz0 ^ n = a.toMul
    apply Units.ext
    exact hz

/-- An algebraic complex character extends along any injective homomorphism
of abelian groups, with no finiteness or universe restriction on the domain. -/
theorem exists_complex_character_extension
    {A : Type u} [CommGroup A] {B : Type v} [CommGroup B]
    (f : A →* B) (hf : Function.Injective f) (η : A →* ℂˣ) :
    ∃ χ : B →* ℂˣ, χ.comp f = η := by
  let : DivisibleBy (Additive ℂˣ) ℕ := complexUnitsDivisibleByNat
  let : DivisibleBy (Additive ℂˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨χ, hχ⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    f.toAdditive hf η.toAdditive
  refine ⟨MonoidHom.toAdditive.symm χ, ?_⟩
  apply MonoidHom.ext
  intro a
  exact congrArg Additive.toMul (DFunLike.congr_fun hχ (Additive.ofMul a))

/-- An algebraic homomorphism continuous on an open subgroup is continuous. -/
theorem continuous_monoidHom_of_open_subgroup
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    {B : Type v} [Monoid B] [TopologicalSpace B] [ContinuousMul B]
    (N : Subgroup A) (hN : IsOpen (N : Set A)) (χ : A →* B)
    (hχ : Continuous (χ.comp N.subtype)) : Continuous χ := by
  apply continuous_of_continuousAt_one χ
  exact hN.isOpenEmbedding_subtypeVal.continuousAt_iff.mp (hχ.continuousAt (x := 1))

/-- Every continuous complex character on an open subgroup of an abelian
topological group extends continuously to the whole group. -/
theorem exists_continuous_complex_character_extension
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    (N : Subgroup A) (hN : IsOpen (N : Set A)) (η : N →ₜ* ℂˣ) :
    ∃ χ : A →ₜ* ℂˣ, ∀ x : N, χ x = η x := by
  obtain ⟨χ, hχ⟩ := exists_complex_character_extension N.subtype Subtype.val_injective
    η.toMonoidHom
  have hc : Continuous χ := continuous_monoidHom_of_open_subgroup N hN χ (by
    rw [hχ]
    exact η.continuous)
  exact ⟨⟨χ, hc⟩, fun x ↦ DFunLike.congr_fun hχ x⟩

/-- Descend and extend a continuous complex character along an open homomorphism.
Compatibility is exactly triviality on the kernel, with no finite-index premise. -/
theorem exists_continuous_complex_character_of_open_map
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    {B : Type v} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B]
    (f : A →ₜ* B) (hf : IsOpenMap f) (η : A →ₜ* ℂˣ)
    (hker : f.toMonoidHom.ker ≤ η.toMonoidHom.ker) :
    ∃ χ : B →ₜ* ℂˣ, χ.comp f = η := by
  let g := f.toMonoidHom.rangeRestrict
  have hgker : g.ker ≤ η.toMonoidHom.ker := by
    intro a ha
    apply hker
    exact congrArg Subtype.val ha
  let ψ : f.toMonoidHom.range →* ℂˣ :=
    g.liftOfSurjective f.toMonoidHom.rangeRestrict_surjective ⟨η.toMonoidHom, hgker⟩
  have hψ (a : A) : ψ (g a) = η a :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hq : Topology.IsQuotientMap g :=
    (hf.codRestrict _).isQuotientMap
      (f.continuous.subtype_mk _) f.toMonoidHom.rangeRestrict_surjective
  have hcψ : Continuous ψ := hq.continuous_iff.mpr (by
    convert η.continuous using 1
    exact funext hψ)
  have hopen : IsOpen (f.toMonoidHom.range : Set B) := by
    change IsOpen (Set.range f)
    simpa only [Set.image_univ] using hf Set.univ isOpen_univ
  obtain ⟨χ, hχ⟩ := exists_continuous_complex_character_extension _ hopen ⟨ψ, hcψ⟩
  refine ⟨χ, ?_⟩
  apply ContinuousMonoidHom.ext
  intro a
  exact (hχ (g a)).trans (hψ a)

end Langlands.Topology
