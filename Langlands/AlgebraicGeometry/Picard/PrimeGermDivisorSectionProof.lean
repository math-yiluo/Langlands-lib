import Langlands.AlgebraicGeometry.Picard.AssociatedEquationGluing
import Langlands.AlgebraicGeometry.Picard.PrimeDivisorEquations
import Langlands.AlgebraicGeometry.Picard.PrimeGermDivisorSectionStatement

/-! # Proof of the prime-germ divisor-section statement -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule PrimeDivisor

set_option backward.isDefEq.respectTransparency false in
/-- The geometric construction of a prime-germ section, conditional only on gluing
nonzero local equations whose germs are associated on overlaps. -/
theorem primeGermDivisorSection_of_gluing
    (hglue : ∀ (X : Scheme.{u}) [IsIntegral X] (ι : Type u) (T : ι → X.Opens),
      (⨆ i, T i) = ⊤ → ∀ a : ∀ i, Γ(X, T i),
      (∀ i x (hx : x ∈ T i), X.presheaf.germ (T i) x hx (a i) ≠ 0) →
      (∀ i j x (hxi : x ∈ T i) (hxj : x ∈ T j),
        Associated (X.presheaf.germ (T i) x hxi (a i))
          (X.presheaf.germ (T j) x hxj (a j))) →
      ∃ (L : LineBundle X) (s : GlobalSections L.obj),
        (∀ i, T i ⊓ trivializationOpen L.obj s = X.basicOpen (a i)) ∧
        ∀ i (Y : Scheme.{u}) (g : Y ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ T i),
          VanishesAlong L g s ↔ g.appLE (T i) ⊤ hg (a i) = 0) :
    PrimeGermDivisorSectionStatement.{u} := by
  classical
  intro X _ _ hufd e π hπ
  obtain ⟨ζ, hζe, hζ, hbasic⟩ := exists_primeGermPoint e π hπ
  choose U hxU a ha0 ha using exists_affine_equation ζ hζ hufd
  let T : X → X.Opens := fun x ↦ (U x).1
  have hT : (⨆ x, T x) = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  have hreg : ∀ i x (hx : x ∈ T i), X.presheaf.germ (T i) x hx (a i) ≠ 0 := by
    intro i x hx h
    apply ha0 i
    apply germ_injective_of_isIntegral X x hx
    simpa only [map_zero] using h
  have hassoc : ∀ i j x (hxi : x ∈ T i) (hxj : x ∈ T j),
      Associated (X.presheaf.germ (T i) x hxi (a i))
        (X.presheaf.germ (T j) x hxj (a j)) := by
    intro i j x hxi hxj
    exact associated_equation_germs (closureIdeal ζ) (U i) (U j)
      (a i) (a j) (ha i) (ha j) x hxi hxj
  obtain ⟨L, s, hgen, hvan⟩ := hglue X X T hT a hreg hassoc
  refine ⟨L, s, ?_, ?_, ?_, ?_⟩
  · intro he
    have hea : e ∈ X.basicOpen (a e) := by
      rw [← hgen e]
      exact ⟨hxU e, he⟩
    exact (mem_basicOpen_equation_iff ζ (U e) (a e) (ha e) e (hxU e)).mp hea hζe
  · have hne : X.basicOpen (a e) ≠ ⊥ :=
      fun h ↦ ha0 e ((basicOpen_eq_bot_iff (a e)).mp h)
    obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
    rw [← hgen e] at hx
    exact ⟨x, hx.2⟩
  · intro V heV f hdiv x hxf
    have hζnotf : ζ ∉ X.basicOpen f :=
      fun hz ↦ (hbasic V heV f).mp hz hdiv
    have hnot : ¬ ζ ⤳ x :=
      fun hspec ↦ hζnotf (hspec.mem_open (X.basicOpen f).isOpen hxf)
    have hxa : x ∈ X.basicOpen (a x) :=
      (mem_basicOpen_equation_iff ζ (U x) (a x) (ha x) x (hxU x)).mpr hnot
    rw [← hgen x] at hxa
    exact hxa.2
  · exact ⟨T e, hxU e, a e,
      associated_equation_germ_prime ζ e hζe π hπ hbasic (U e) (hxU e)
        (a e) (ha0 e) (ha e), hvan e⟩

/-- On an integral locally Noetherian scheme with factorial stalks, a prime germ `π` at `e`
gives a line bundle with a global section cutting out the prime divisor of `π`. -/
theorem primeGermDivisorSection : PrimeGermDivisorSectionStatement.{u} :=
  primeGermDivisorSection_of_gluing fun _ _ _ T hT a hreg hassoc ↦
    exists_lineBundle_of_associated_equations T hT a hreg hassoc

end Langlands.AlgebraicGeometry.Picard
