import Langlands.GroupScheme.Torus.FiniteCharacterSeparation
import Langlands.GroupScheme.Torus.NormalizerLifting

/-! # Finite torsion tests for diagonalizable normalizers -/

noncomputable section

universe u

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.CharacterAction

open Corepresented

variable {R : CommRingCat.{u}} {M N : Type u} [AddCommGroup M] [AddCommGroup N]
  {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} (emb : CharacterEmbedding F M)

/-- Change character degrees without changing coefficients. -/
def degreeMap (q : M →+ N) (A : CommAlgCat.{u} R) :
    algebra (M := M) A ⟶ algebra (M := N) A :=
  evaluate (constant A) ((universal A).comp (AddMonoidHom.toMultiplicative q))

@[simp] theorem degreeMap_single (q : M →+ N) (A : CommAlgCat.{u} R) (m : M) (a : A) :
    (degreeMap q A).hom (AddMonoidAlgebra.single m a) = AddMonoidAlgebra.single (q m) a := by
  rw [degreeMap, evaluate_single]
  change AddMonoidAlgebra.single 0 a * AddMonoidAlgebra.single (q m) 1 = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

/-- Degree change is the usual group-algebra pushforward. -/
theorem degreeMap_apply (q : M →+ N) (A : CommAlgCat.{u} R) (w : AddMonoidAlgebra A M) :
    (degreeMap q A).hom w = AddMonoidAlgebra.mapDomain q w := by
  have h : (degreeMap q A).hom.toRingHom = AddMonoidAlgebra.mapDomainRingHom A q := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro a
      change (degreeMap q A).hom (AddMonoidAlgebra.single 0 a) =
        AddMonoidAlgebra.mapDomain q (AddMonoidAlgebra.single 0 a)
      rw [degreeMap_single, AddMonoidAlgebra.mapDomain_single]
    · intro m
      change (degreeMap q A).hom (AddMonoidAlgebra.single m 1) =
        AddMonoidAlgebra.mapDomain q (AddMonoidAlgebra.single m 1)
      rw [degreeMap_single, AddMonoidAlgebra.mapDomain_single]
  exact RingHom.congr_fun h w

/-- Conjugate the universal embedded character by an arbitrary parameter point. -/
def universalEmbeddedConjugate {A : CommAlgCat.{u} R} (g : F.obj A) : F.obj (algebra (M := M) A) :=
  F.map (constant A) g * emb.hom _ (universal A) * (F.map (constant A) g)⁻¹

/-- Character ranges are preserved under coefficient algebra maps. -/
theorem CharacterEmbedding.map_mem_range {A C : CommAlgCat.{u} R} (f : A ⟶ C)
    {g : F.obj A} (hg : g ∈ emb.range A) : F.map f g ∈ emb.range C := by
  obtain ⟨t, rfl⟩ := hg
  exact ⟨mapCharacter f t, (emb.naturality f t).symm⟩

/-- All-test normalization can be tested on the universal embedded character
for the point and its inverse. -/
theorem mem_normalizerFamily_iff_universalEmbedded {A : CommAlgCat.{u} R} (g : F.obj A) :
    g ∈ normalizerFamily emb.range A ↔
      universalEmbeddedConjugate emb g ∈ emb.range (algebra A) ∧
        universalEmbeddedConjugate emb g⁻¹ ∈ emb.range (algebra A) := by
  constructor
  · intro hg
    have h := hg _ (constant A) (emb.hom _ (universal A)) ⟨universal A, rfl⟩
    simpa only [universalEmbeddedConjugate, map_inv, inv_inv] using h
  · rintro ⟨hg, hgi⟩ D f x ⟨t, rfl⟩
    have hmap (y : F.obj A) :
        F.map (evaluate f t) (universalEmbeddedConjugate emb y) =
          F.map f y * emb.hom D t * (F.map f y)⁻¹ := by
      simp only [universalEmbeddedConjugate, map_mul, map_inv,
        ← ConcreteCategory.comp_apply, ← F.map_comp, constant_evaluate,
        emb.naturality, mapCharacter_evaluate_universal]
    refine ⟨?_, ?_⟩
    · simpa only [hmap] using emb.map_mem_range (evaluate f t) hg
    · simpa only [hmap, map_inv, inv_inv] using emb.map_mem_range (evaluate f t) hgi

/-- The support can only shrink under a coefficient algebra map. -/
theorem coefficientMap_support_subset {A C : CommAlgCat.{u} R} (f : A ⟶ C)
    (w : AddMonoidAlgebra A M) :
    ((coefficientMap f).hom w).coeff.support ⊆ w.coeff.support := by
  intro m hm
  apply Finsupp.mem_support_iff.mpr
  intro hz
  apply Finsupp.mem_support_iff.mp hm
  rw [coefficientMap_coeff, hz, map_zero]

/-- The universal conjugate commutes with change of parameter coefficients. -/
theorem universalEmbeddedConjugate_map {A C : CommAlgCat.{u} R} (f : A ⟶ C) (g : F.obj A) :
    F.map (coefficientMap f) (universalEmbeddedConjugate emb g) =
      universalEmbeddedConjugate emb (F.map f g) := by
  simp only [universalEmbeddedConjugate, map_mul, map_inv, emb.naturality,
    mapCharacter_coefficientMap_universal, ← ConcreteCategory.comp_apply, ← F.map_comp,
    constant_coefficientMap]

/-- Its classifying coordinate functions also specialize coefficientwise. -/
theorem universalEmbeddedConjugate_classifying_map
    {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    {A C : CommAlgCat.{u} R} (f : A ⟶ C) (g : F.obj A) (b : B) :
    (e.homEquiv.symm (universalEmbeddedConjugate emb (F.map f g))).hom b =
      (coefficientMap f).hom ((e.homEquiv.symm (universalEmbeddedConjugate emb g)).hom b) := by
  rw [← universalEmbeddedConjugate_map, homEquiv_symm_map]
  rfl

/-- An integer character quotient detects normalization when testing the two
universal conjugates after degree reduction is sufficient on every algebra. -/
def FiniteDegreeDetectsNormalizer (n : ℕ) : Prop :=
  ∀ (A : CommAlgCat.{u} R) (g : F.obj A),
    g ∈ normalizerFamily emb.range A ↔
      F.map (degreeMap (QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples n)) A)
          (universalEmbeddedConjugate emb g) ∈
            emb.range (algebra (M := M ⧸ FiniteCharacterSeparation.multiples n) A) ∧
      F.map (degreeMap (QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples n)) A)
          (universalEmbeddedConjugate emb g⁻¹) ∈
            emb.range (algebra (M := M ⧸ FiniteCharacterSeparation.multiples n) A)

/-- Finitely many subgroup equations admit one finite character-degree test
for all normalizing parameter points. -/
theorem exists_finiteDegreeDetectsNormalizer [AddGroup.FG M]
    {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    {I : Ideal B} (hI : IsCutOutBy e emb.range I) (hIfg : I.FG) :
    ∃ n : ℕ, 0 < n ∧ FiniteDegreeDetectsNormalizer emb n := by
  classical
  obtain ⟨T, hT⟩ := hIfg
  let u : F.obj B := e.homEquiv (𝟙 B)
  let coeff (g : F.obj B) (b : B) : AddMonoidAlgebra B M :=
    (e.homEquiv.symm (universalEmbeddedConjugate emb g)).hom b
  let S : Finset M := T.biUnion fun b => (coeff u b).coeff.support ∪ (coeff u⁻¹ b).coeff.support
  obtain ⟨n, hn, hsep⟩ := FiniteCharacterSeparation.exists_separates S
  let Q := M ⧸ FiniteCharacterSeparation.multiples n
  let q : M →+ Q := QuotientAddGroup.mk' (FiniteCharacterSeparation.multiples n)
  have hq : Set.InjOn q (S : Set M) := hsep
  have lift_mem (g₀ : F.obj B)
      (hS : ∀ b ∈ T, (coeff g₀ b).coeff.support ⊆ S)
      (A : CommAlgCat.{u} R) (f : B ⟶ A)
      (h : F.map (degreeMap q A) (universalEmbeddedConjugate emb (F.map f g₀)) ∈
        emb.range (algebra (M := Q) A)) :
      universalEmbeddedConjugate emb (F.map f g₀) ∈ emb.range (algebra A) := by
    let y := universalEmbeddedConjugate emb (F.map f g₀)
    have hgens : ∀ b ∈ T, (e.homEquiv.symm y).hom b = 0 := by
      intro b hb
      have hzero := (hI _ _).mp h b (by rw [← hT]; exact Ideal.subset_span hb)
      rw [homEquiv_symm_map] at hzero
      change (degreeMap q A).hom ((e.homEquiv.symm y).hom b) = 0 at hzero
      rw [degreeMap_apply] at hzero
      apply (FiniteCharacterSeparation.mapDomain_eq_zero_iff_of_support q (S : Set M) hq
        ((e.homEquiv.symm y).hom b) ?_).mp hzero
      change ((e.homEquiv.symm (universalEmbeddedConjugate emb (F.map f g₀))).hom b).coeff.support ⊆ S
      rw [universalEmbeddedConjugate_classifying_map]
      exact (coefficientMap_support_subset f (coeff g₀ b)).trans (hS b hb)
    have hker : I ≤ RingHom.ker (e.homEquiv.symm y).hom.toRingHom := by
      rw [← hT, Ideal.span_le]
      exact hgens
    exact (hI _ _).mpr (fun b hb => hker hb)
  refine ⟨n, hn, fun A g => ?_⟩
  constructor
  · intro hg
    have h := (mem_normalizerFamily_iff_universalEmbedded emb g).mp hg
    exact ⟨emb.map_mem_range (degreeMap q A) h.1, emb.map_mem_range (degreeMap q A) h.2⟩
  · intro hg
    obtain ⟨f, rfl⟩ := e.homEquiv.surjective g
    have hu : F.map f u = e.homEquiv f := by
      change F.map f (e.homEquiv (𝟙 B)) = e.homEquiv f
      have h := e.homEquiv_comp f (𝟙 B)
      rw [Category.id_comp] at h
      exact h.symm
    apply (mem_normalizerFamily_iff_universalEmbedded emb _).mpr
    constructor
    · rw [← hu]
      apply lift_mem u ?_ A f (by simpa only [hu] using hg.1)
      intro b hb m hm
      exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_union_left _ hm⟩
    · have hui : F.map f u⁻¹ = (e.homEquiv f)⁻¹ := by rw [map_inv, hu]
      rw [← hui]
      apply lift_mem u⁻¹ ?_ A f (by simpa only [hui] using hg.2)
      intro b hb m hm
      exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_union_right _ hm⟩

end Langlands.GroupScheme.CharacterAction
