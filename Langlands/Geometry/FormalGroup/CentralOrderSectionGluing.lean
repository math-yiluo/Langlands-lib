import Langlands.Geometry.FormalGroup.CentralNumeratorSection
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Gluing the central scalar law of an actual rational order section -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.RationalSection

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {F K : Type v} [Field F] [Algebra O F] [IsFractionRing O F] [Field K] [Algebra C K]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : OrderAction D M} {G : OrderAction D N}
variable {hs : ∀ (a : C) (x : σ → R),
  E.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x}
variable {ht : ∀ (a : C) (x : τ → R),
  G.fiberTangent (RingHom.id R) (algebraMap C D a) x = algebraMap C R a • x}
variable {U : Opens (PrimeSpectrum R)} {p : ℕ}

/-- The witnesses of a local quasi-isogeny become order-linear numerators on each witnessing open. -/
theorem exists_orderScalarPresentation (z : LocalQuasiIsogeny F (p : O) M N U)
    (hz : IsOrderLinear E G z.val) (hπ : Irreducible (p : O)) (x : U) :
    ∃ (V : Opens (PrimeSpectrum R)) (_hx : x.val ∈ V) (i : V ⟶ U),
      Nonempty (OrderScalarPresentation p E G (restrict i z.val)) := by
  obtain ⟨V, hx, i, n, f, hf, he⟩ := z.isLocal x.val x.property
  have he' : (p : F) ^ n • restrict i z.val = ofIntegral V f := by simpa only [map_natCast] using he
  exact ⟨V, hx, i, ⟨⟨n, integralOrderHomOfScalar hπ z.source_divisible hz i _ f he', hf, he'⟩⟩⟩

/-- A central scalar change agrees with the centralized numerator on every presenting open. -/
def IsCentralScalarChange (z : RationalSection F M N U)
    (s : RationalSection K (E.centralModule hs) (G.centralModule ht) U) (p : ℕ) : Prop :=
  ∀ (V : Opens (PrimeSpectrum R)) (i : V ⟶ U) (P : OrderScalarPresentation p E G (restrict i z)),
    restrict i s = P.centralSection

/-- The local numerator descriptions glue uniquely, with no choice of an integral denominator globally. -/
theorem existsUnique_centralScalarChange (z : LocalQuasiIsogeny F (p : O) M N U)
    (hz : IsOrderLinear E G z.val) (hπ : Irreducible (p : O)) (hp : (p : K) ≠ 0) :
    ∃! s : RationalSection K (E.centralModule hs) (G.centralModule ht) U, IsCentralScalarChange z.val s p := by
  choose V hx i ho using fun x : U => exists_orderScalarPresentation z hz hπ x
  let P (x : U) := Classical.choice (ho x)
  let H := rationalHomTypeSheaf K (E.centralModule hs) (G.centralModule ht)
  let s (x : U) := (P x).centralSection (K := K) (hs := hs) (ht := ht)
  have hc : U ≤ iSup V := fun x h => (le_iSup V ⟨x, h⟩) (hx ⟨x, h⟩)
  have hcompat : TopCat.Presheaf.IsCompatible H.obj V s := by
    intro x y
    apply (P x).centralSection_restrict_eq (P y) _ _ hp hπ z.source_divisible
    rw [← restrict_comp, ← restrict_comp]
    rfl
  obtain ⟨t, htGlue, htUnique⟩ := H.existsUnique_gluing' V U i hc s hcompat
  change RationalSection K (E.centralModule hs) (G.centralModule ht) U at t
  change ∀ x, restrict (i x) t = s x at htGlue
  refine ⟨t, ?_, fun t' ht' => htUnique t' (fun x => ht' (V x) (i x) (P x))⟩
  intro W j Q
  let W' (x : U) := W ⊓ V x
  let u (x : U) : W' x ⟶ W := homOfLE inf_le_left
  let v (x : U) : W' x ⟶ V x := homOfLE inf_le_right
  have hc' : W ≤ iSup W' := by
    intro x hW
    let a : U := ⟨x, (leOfHom j) hW⟩
    exact (le_iSup W' a) ⟨hW, hx a⟩
  apply H.eq_of_locally_eq' W' W u hc'
  intro x
  change restrict (u x) (restrict j t) = restrict (u x) Q.centralSection
  have hi : u x ≫ j = v x ≫ i x := Subsingleton.elim _ _
  rw [← restrict_comp, hi, restrict_comp, htGlue x]
  apply (P x).centralSection_restrict_eq Q (v x) (u x) hp hπ z.source_divisible
  rw [← restrict_comp, ← restrict_comp, hi]

/-- The actual central rational section glued from the isogeny numerators. -/
def centralScalarSection (z : LocalQuasiIsogeny F (p : O) M N U)
    (hz : IsOrderLinear E G z.val) (hπ : Irreducible (p : O)) (hp : (p : K) ≠ 0) :
    RationalSection K (E.centralModule hs) (G.centralModule ht) U :=
  (existsUnique_centralScalarChange z hz hπ hp).exists.choose

theorem centralScalarSection_isCentralScalarChange (z : LocalQuasiIsogeny F (p : O) M N U)
    (hz : IsOrderLinear E G z.val) (hπ : Irreducible (p : O)) (hp : (p : K) ≠ 0) :
    IsCentralScalarChange z.val (centralScalarSection (hs := hs) (ht := ht) z hz hπ hp) p :=
  (existsUnique_centralScalarChange z hz hπ hp).exists.choose_spec

end Langlands.FormalGroup.ModuleLaw.RationalSection
