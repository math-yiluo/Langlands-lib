import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientIndependence
import Langlands.Representation.Plancherel.DiscreteSeriesOrbits
import Langlands.Representation.Category.ClassInvariants
import Langlands.Weil.Representation.ContinuityProof

/-! # Finiteness of the discrete-series orbits with fixed vectors (Waldspurger, VIII.5)

Waldspurger, VIII.5 (printed pp. 331–332), proof of Theorem VIII.1.2. For a compact open
subgroup `H` of `G`, let `Â_G^H` be the unitary characters of `A_G` trivial on `A_G ∩ H`. The
quotient `Â_G^H / Im X(G)` is finite; choosing representatives `X`, the map
`⋃_{χ ∈ X} E₂(G)^H_χ → Θ^H_G` sending `ω` to its orbit is surjective, so it suffices that each
`E₂(G)^H_χ` is finite, which follows from Theorem VIII.4.2 and Proposition VIII.4.1.

This module formalizes this reduction in the Library's framework of discrete-series classes
(`DiscreteSeriesClass A hA μ`, a central subgroup `A` in place of `A_G`) and their orbits under
the unitary unramified characters `unitaryUnramifiedCharacters ν` (Waldspurger's `Im X(G)`):

* `finite_image_mk_characterAnnihilator`: if `K` is compact and `U` open normal, the characters
  trivial on `U` have finitely many classes modulo the characters trivial on `K` (with `K` the
  intersection of `A` with the common norm kernel, this is the finiteness of
  `Â_G^H / Im X(G)`);
* `finite_image_orbitRel_of_finite`: an abstract counting lemma for the surjection above;
* `finite_discreteSeriesFixedOrbits`: `Θ^H_G` is finite if every `E₂(G)^H_χ` is finite;
* `finite_discreteSeriesCentralFixed_of_coefficient_mem`: `E₂(G)^H_χ` is finite if the
  `H`-bi-invariant elements of its coefficient spaces lie in one finite-dimensional space
  (Waldspurger's `p_χ(°C_H)`);
* `finite_discreteSeriesFixedOrbits_of_coefficient_mem`: the two combined.

The existence of the finite-dimensional space (Proposition VIII.4.1 and the inclusion of
Theorem VIII.4.2) is a hypothesis, as are the compactness of `A ∩ G¹` and the surjectivity of
the restriction of `Im X(G)` onto the unitary characters of `A` trivial on `A ∩ G¹`.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel

universe uG uV uI

section Characters

variable {A : Type*} [Group A]

/-- The subgroup of characters `A → ℂˣ` trivial on the subgroup `K`. -/
def characterAnnihilator (K : Subgroup A) : Subgroup (A →* ℂˣ) where
  carrier := {χ | ∀ k ∈ K, χ k = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {χ η} hχ hη k hk => by
    rw [MonoidHom.mul_apply, hχ k hk, hη k hk, mul_one]
  inv_mem' := fun {χ} hχ k hk => by
    rw [MonoidHom.inv_apply, hχ k hk, inv_one]

theorem mem_characterAnnihilator {K : Subgroup A} {χ : A →* ℂˣ} :
    χ ∈ characterAnnihilator K ↔ ∀ k ∈ K, χ k = 1 :=
  Iff.rfl

/-- If the restrictions to `K` of the elements of `S` form a finite set, then `S` has finitely
many classes modulo the characters trivial on `K`. -/
theorem finite_image_mk_of_finite_image_restrict (K : Subgroup A) {S : Set (A →* ℂˣ)}
    (hS : ((fun χ : A →* ℂˣ => χ.comp K.subtype) '' S).Finite) :
    ((QuotientGroup.mk : (A →* ℂˣ) → (A →* ℂˣ) ⧸ characterAnnihilator K) '' S).Finite := by
  classical
  let r : (A →* ℂˣ) → (K →* ℂˣ) := fun χ => χ.comp K.subtype
  let g : (K →* ℂˣ) → (A →* ℂˣ) ⧸ characterAnnihilator K := fun ψ =>
    if h : ∃ χ ∈ S, r χ = ψ then QuotientGroup.mk h.choose else 1
  refine (hS.image g).subset ?_
  rintro _ ⟨χ, hχ, rfl⟩
  refine ⟨r χ, ⟨χ, hχ, rfl⟩, ?_⟩
  have h : ∃ χ' ∈ S, r χ' = r χ := ⟨χ, hχ, rfl⟩
  simp only [g, h, ↓reduceDIte]
  obtain ⟨-, hr⟩ := h.choose_spec
  rw [QuotientGroup.eq]
  intro k hk
  have hk' := DFunLike.congr_fun hr ⟨k, hk⟩
  simp only [r, MonoidHom.comp_apply, Subgroup.coe_subtype] at hk'
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hk', inv_mul_cancel]

variable [TopologicalSpace A] [IsTopologicalGroup A]

/-- If `K` is compact and `U` is an open normal subgroup, the restrictions to `K` of the
characters trivial on `U` form a finite set: they are trivial on the finite-index subgroup
`U ∩ K` of `K`, so they take values in the `[K : U ∩ K]`-th roots of unity and are determined
by their values on representatives of `K / (U ∩ K)`. -/
theorem finite_restrict_of_isCompact (K U : Subgroup A) [U.Normal] (hK : IsCompact (K : Set A))
    (hU : IsOpen (U : Set A)) :
    ((fun χ : A →* ℂˣ => χ.comp K.subtype) '' {χ | ∀ u ∈ U, χ u = 1}).Finite := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hUK : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := Subgroup.subgroupOf_isOpen K U hU
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hUK
  have hn : U.relIndex K ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : NeZero (U.relIndex K) := ⟨hn⟩
  let T : Set (K →* ℂˣ) := {ψ | ∀ k : K, (k : A) ∈ U → ψ k = 1}
  have hsub : (fun χ : A →* ℂˣ => χ.comp K.subtype) '' {χ | ∀ u ∈ U, χ u = 1} ⊆ T := by
    rintro _ ⟨χ, hχ, rfl⟩ k hk
    exact hχ _ hk
  refine Set.Finite.subset ?_ hsub
  let Φ : T → (K ⧸ U.subgroupOf K → rootsOfUnity (U.relIndex K) ℂ) := fun ψ q =>
    ⟨ψ.1 q.out, by
      rw [mem_rootsOfUnity, ← map_pow]
      exact ψ.2 _ (by
        rw [Subgroup.coe_pow]
        exact U.pow_relIndex_mem q.out.2)⟩
  have hΦ : Function.Injective Φ := by
    intro ψ ψ' h
    apply Subtype.ext
    ext k : 1
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf K) k
    have h1 := congrArg (fun F => ((F (QuotientGroup.mk k) : rootsOfUnity _ ℂ) : ℂˣ)) h
    simp only [Φ] at h1
    have hu' : ((u : K) : A) ∈ U := Subgroup.mem_subgroupOf.mp u.2
    rw [hu, map_mul, map_mul, ψ.2 _ hu', ψ'.2 _ hu', mul_one, mul_one] at h1
    exact h1
  have : Finite T := Finite.of_injective Φ hΦ
  exact Set.toFinite T

/-- **Finiteness of `Â^H / Im X`** (Waldspurger, VIII.5, printed p. 331): for `K` compact and `U`
open normal, the characters trivial on `U` have finitely many classes modulo the characters
trivial on `K`. -/
theorem finite_image_mk_characterAnnihilator (K U : Subgroup A) [U.Normal]
    (hK : IsCompact (K : Set A)) (hU : IsOpen (U : Set A)) :
    ((QuotientGroup.mk : (A →* ℂˣ) → (A →* ℂˣ) ⧸ characterAnnihilator K) ''
      {χ | ∀ u ∈ U, χ u = 1}).Finite :=
  finite_image_mk_of_finite_image_restrict K (finite_restrict_of_isCompact K U hK hU)

end Characters

section Counting

/-- **Counting lemma.** Let `X` act on `E`, and let every `e` with `P e` carry a "character"
`c e` in a commutative group `C`, related to `e` by `rel`. Suppose that `P` is `X`-invariant,
that two elements whose characters agree modulo `R` can be moved by `X` so that the first acquires
the character of the second, that the characters of the elements with `P` have finitely many
classes modulo `R`, and that each fibre `{e' | P e' ∧ rel e' (c e)}` is finite. Then finitely
many `X`-orbits meet `{e | P e}`. -/
theorem finite_image_orbitRel_of_finite {X E C : Type*} [Group X] [MulAction X E] [CommGroup C]
    (R : Subgroup C) (P : E → Prop) (rel : E → C → Prop) (c : E → C)
    (hP : ∀ (x : X) (e : E), P e → P (x • e))
    (hadj : ∀ e e', P e → P e' → (c e)⁻¹ * c e' ∈ R → ∃ x : X, rel (x • e) (c e'))
    (himage : ((QuotientGroup.mk : C → C ⧸ R) '' (c '' {e | P e})).Finite)
    (hfib : ∀ e, P e → {e' | P e' ∧ rel e' (c e)}.Finite) :
    ((Quotient.mk (MulAction.orbitRel X E)) '' {e | P e}).Finite := by
  classical
  let S := (QuotientGroup.mk : C → C ⧸ R) '' (c '' {e | P e})
  have hrep : ∀ s : S, ∃ e, P e ∧ (QuotientGroup.mk (c e) : C ⧸ R) = s := by
    rintro ⟨s, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, rfl⟩
  choose g hgP hgc using hrep
  have : Finite S := himage.to_subtype
  refine (Set.finite_iUnion fun s : S =>
    ((hfib (g s) (hgP s)).image (Quotient.mk (MulAction.orbitRel X E)))).subset ?_
  rintro _ ⟨e, he, rfl⟩
  let s : S := ⟨QuotientGroup.mk (c e), ⟨c e, ⟨e, he, rfl⟩, rfl⟩⟩
  have hmk : (QuotientGroup.mk (c (g s)) : C ⧸ R) = QuotientGroup.mk (c e) := hgc s
  obtain ⟨x, hx⟩ := hadj e (g s) he (hgP s) (QuotientGroup.eq.mp hmk.symm)
  refine Set.mem_iUnion.mpr ⟨s, x • e, ⟨hP x e he, hx⟩, ?_⟩
  exact Quotient.sound ⟨x, rfl⟩

end Counting

section Classes

variable {G : Type uG} [Group G] [TopologicalSpace G]

omit [TopologicalSpace G] in
theorem actsByCharacter_of_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (A : Subgroup G) (χ : A →* ℂˣ) (h : ∀ (a : A) (v : V), ρ (a : G) v = (χ a : ℂ) • v)
    (a : A) (w : W) : σ (a : G) w = (χ a : ℂ) • w := by
  obtain ⟨v, rfl⟩ := e.surjective w
  calc σ (a : G) (e v) = e (ρ (a : G) v) :=
        (congrArg (fun f : V →ₗ[ℂ] W => f v) (e.isIntertwining' (a : G))).symm
    _ = (χ a : ℂ) • e v := by rw [h a v, map_smul]

/-- The subgroup `A` acts on (any representative of) the class by the character `χ`. For `A`
central and `ω` a discrete-series class, this says that the central character of `ω`
restricted to `A` is `χ` (Waldspurger's `E₂(G)_χ`, VIII.4, printed p. 330). -/
def classActsByCharacter (A : Subgroup G) (χ : A →* ℂˣ) :
    SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G) → Prop :=
  Quotient.lift
    (fun π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G) =>
      ∀ (a : A) (v : π.obj), π.obj.representation (a : G) v = (χ a : ℂ) • v)
    (by
      rintro π σ ⟨e⟩
      have e' := SmoothRep.equivOfIso ((irreducibleAdmissibleProperty (k := ℂ) (G := G)).ι.mapIso e)
      exact propext ⟨actsByCharacter_of_equiv e' A χ, actsByCharacter_of_equiv e'.symm A χ⟩)

theorem classActsByCharacter_mk (A : Subgroup G) (χ : A →* ℂˣ)
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G)) :
    classActsByCharacter A χ (Quotient.mk _ π) ↔
      ∀ (a : A) (v : π.obj), π.obj.representation (a : G) v = (χ a : ℂ) • v :=
  Iff.rfl

/-- If `A` acts by `χ` and the class has a nonzero `H`-fixed vector, then `χ` is trivial on
`A ∩ H`. -/
theorem classActsByCharacter_eq_one {A : Subgroup G} {χ : A →* ℂˣ} {H : Subgroup G}
    {ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)} (hχ : classActsByCharacter A χ ω)
    (hH : SmoothDualClass.HasFixedVector H ω) (a : A) (ha : (a : G) ∈ H) : χ a = 1 := by
  induction ω using Quotient.inductionOn with
  | h π =>
    obtain ⟨v, hv, hv0⟩ := (fixedVectors π.obj.representation H).ne_bot_iff.mp hH
    have hfix : π.obj.representation (a : G) v = v :=
      (Representation.mem_invariants _ v).mp hv ⟨a, ha⟩
    have h1 : ((χ a : ℂ) - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hχ a v, hfix, sub_self]
    have h2 : (χ a : ℂ) = 1 := sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hv0)
    exact Units.ext h2

/-- Twisting by a character `η` multiplies the character by which `A` acts by the restriction of
`η` to `A`. -/
theorem classActsByCharacter_twist {A : Subgroup G} {χ : A →* ℂˣ} (η : G →* ℂˣ)
    (hη : IsOpen (η.ker : Set G)) {ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)}
    (hχ : classActsByCharacter A χ ω) :
    classActsByCharacter A (η.comp A.subtype * χ) (SmoothDualClass.twist η hη ω) := by
  induction ω using Quotient.inductionOn with
  | h π =>
    intro a v
    change (η a : ℂ) • π.obj.representation (a : G) v = ((η a * χ a : ℂˣ) : ℂ) • v
    rw [Units.val_mul, mul_smul]
    exact congrArg _ (hχ a v)

/-- Twisting by a character trivial on `H` preserves the existence of a nonzero `H`-fixed
vector. -/
theorem hasFixedVector_twist {H : Subgroup G} (η : G →* ℂˣ) (hη : IsOpen (η.ker : Set G))
    (hηH : ∀ h ∈ H, η h = 1) {ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G)}
    (hω : SmoothDualClass.HasFixedVector H ω) :
    SmoothDualClass.HasFixedVector H (SmoothDualClass.twist η hη ω) := by
  induction ω using Quotient.inductionOn with
  | h π =>
    have heq : fixedVectors (Langlands.twist η π.obj.representation) H =
        fixedVectors π.obj.representation H := by
      ext v
      simp only [fixedVectors, Representation.mem_invariants]
      refine forall_congr' fun h => ?_
      change (η h : ℂ) • π.obj.representation (h : G) v = v ↔ _
      rw [hηH h h.2, Units.val_one, one_smul]
      exact Iff.rfl
    change fixedVectors (Langlands.twist η π.obj.representation) H ≠ ⊥
    rw [heq]
    exact hω

variable [IsTopologicalGroup G]
variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
variable [MeasurableSpace (G ⧸ A)]
variable (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ]

/-- Waldspurger's `E₂(G)^H_χ` (VIII.5, printed p. 331): the discrete-series classes on which `A`
acts by `χ` and which have a nonzero vector fixed by `H`. -/
def discreteSeriesCentralFixed (χ : A →* ℂˣ) (H : Subgroup G) :
    Set (DiscreteSeriesClass.{uG, uV} A hA μ) :=
  {ω | classActsByCharacter A χ ω.val ∧ SmoothDualClass.HasFixedVector H ω.val}

/-- Every discrete-series class has a central character: its restriction to `A` is a
homomorphism with open kernel and values of absolute value `1`. -/
theorem exists_classActsByCharacter (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    ∃ χ : A →* ℂˣ, IsOpen (χ.ker : Set A) ∧ (∀ a, ‖(χ a : ℂ)‖ = 1) ∧
      classActsByCharacter A χ ω.val := by
  obtain ⟨ω, hω⟩ := ω
  induction ω using Quotient.inductionOn with
  | h π =>
    obtain ⟨-, c, -⟩ := hω
    refine ⟨c.character.comp (Subgroup.inclusion hA), ?_, fun a => c.norm_eq_one _,
      fun a v => c.acts (Subgroup.inclusion hA a) v⟩
    exact c.isOpen_ker.preimage (continuous_inclusion hA)

/-- **Finiteness of `E₂(G)^H_χ`** (Waldspurger, VIII.5, printed p. 332): if the
`H`-bi-invariant elements of the coefficient spaces `A(ω)` of all `ω ∈ E₂(G)^H_χ` lie in one
finite-dimensional space `F` (for Waldspurger, `p_χ(°C_H)`, by Theorem VIII.4.2 and Proposition
VIII.4.1), then `E₂(G)^H_χ` is finite. The coefficient space is that of the chosen
representative `ω.val.out` of the class. -/
theorem finite_discreteSeriesCentralFixed_of_coefficient_mem (χ : A →* ℂˣ) (H : OpenSubgroup G)
    (hH : IsCompact (H : Set G)) (F : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ F]
    (hF : ∀ ω ∈ discreteSeriesCentralFixed.{uG, uV} A hA μ χ H.toSubgroup,
      ∀ f ∈ coefficientFunctionSpace ω.val.out.obj, IsBiInvariant H.toSubgroup f → f ∈ F) :
    (discreteSeriesCentralFixed.{uG, uV} A hA μ χ H.toSubgroup).Finite := by
  let S := discreteSeriesCentralFixed.{uG, uV} A hA μ χ H.toSubgroup
  have hfin : Finite S := by
    refine finite_of_isBiInvariant_coefficient_mem (fun i : S => i.1.val.out.obj)
      (fun i => i.1.val.out.property.1) ?_ H hH ?_ F (fun i => hF i.1 i.2)
    · rintro i j ⟨e⟩
      have hij : i.1.val = j.1.val := by
        rw [← Quotient.out_eq i.1.val, ← Quotient.out_eq j.1.val]
        exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk (SmoothRep.mkIso e)⟩
      exact Subtype.ext (Subtype.ext hij)
    · intro i
      have h := i.2.2
      rw [← Quotient.out_eq i.1.val] at h
      exact h
  exact Set.toFinite S

end Classes

section Orbits

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
variable [MeasurableSpace (G ⧸ A)]
variable (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ]
variable {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

/-- Waldspurger's `Θ^H_G` (VIII.1, printed p. 321): the orbits of `Im X(G)` in `E₂(G)` whose
members have a nonzero vector fixed by `H`. -/
def discreteSeriesFixedOrbits (H : Subgroup G) :
    Set (DiscreteSeriesOrbitClass.{uG, uI, uV} A hA μ ν) :=
  (Quotient.mk (MulAction.orbitRel _ _)) ''
    {ω : DiscreteSeriesClass.{uG, uV} A hA μ | SmoothDualClass.HasFixedVector H ω.val}

/-- **Theorem VIII.1.2 from the finiteness of the `E₂(G)^H_χ`** (Waldspurger, VIII.5, printed
pp. 331–332). Let `H` be an open subgroup contained in the common norm kernel `G¹`, let
`A ∩ G¹` be compact, and let every continuous unitary character of `A` trivial on `A ∩ G¹` be the
restriction of an element of `Im X(G)`. If `E₂(G)^H_χ` is finite for every continuous unitary
character `χ` of `A` trivial on `A ∩ H`, then `Θ^H_G` is finite. -/
theorem finite_discreteSeriesFixedOrbits (H : Subgroup G) (hHo : IsOpen (H : Set G))
    (hH1 : H ≤ commonNormKernel ν)
    (hA1 : IsCompact ((A ⊓ commonNormKernel ν : Subgroup G) : Set G))
    (hsurj : ∀ χ : A →* ℂˣ, Continuous χ → (∀ a, ‖(χ a : ℂ)‖ = 1) →
      (∀ a : A, (a : G) ∈ commonNormKernel ν → χ a = 1) →
      ∃ η ∈ unitaryUnramifiedCharacters ν, ∀ a : A, η a = χ a)
    (hfin : ∀ χ : A →* ℂˣ, Continuous χ → (∀ a, ‖(χ a : ℂ)‖ = 1) →
      (∀ a : A, (a : G) ∈ H → χ a = 1) →
      (discreteSeriesCentralFixed.{uG, uV} A hA μ χ H).Finite) :
    (discreteSeriesFixedOrbits.{uG, uV} A hA μ ν H).Finite := by
  classical
  choose c hcker hcnorm hcacts using exists_classActsByCharacter.{uG, uV} A hA μ
  have hccont : ∀ ω, Continuous (c ω) := fun ω =>
    Langlands.Weil.continuous_of_open_kernel (c ω) (hcker ω)
  -- the subgroups `A ∩ G¹` and `A ∩ H` of `A`
  let K : Subgroup A := (commonNormKernel ν).comap A.subtype
  let U : Subgroup A := H.comap A.subtype
  have hU : IsOpen (U : Set A) := hHo.preimage continuous_subtype_val
  have hK : IsCompact (K : Set A) := by
    rw [Subtype.isCompact_iff]
    convert hA1 using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxA, hxN⟩
      exact ⟨⟨x, hxA⟩, hxN, rfl⟩
  have hUn : U.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hcomm : (g : G) * n = n * g := (Subgroup.mem_center_iff.mp (hA g.2) n).symm
    have : g * n * g⁻¹ = n := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact hn
  let P : DiscreteSeriesClass.{uG, uV} A hA μ → Prop :=
    fun ω => SmoothDualClass.HasFixedVector H ω.val
  let rel : DiscreteSeriesClass.{uG, uV} A hA μ → (A →* ℂˣ) → Prop :=
    fun ω χ => classActsByCharacter A χ ω.val
  refine finite_image_orbitRel_of_finite (X := unitaryUnramifiedCharacters ν)
    (characterAnnihilator K) P rel c ?_ ?_ ?_ ?_
  · -- `Im X(G)` preserves the existence of `H`-fixed vectors
    intro x ω hω
    exact hasFixedVector_twist _ _ (fun h hh => x.2.1 (hH1 hh)) hω
  · -- adjusting the central character by an element of `Im X(G)`
    intro ω ω' _ _ hR
    set ψ := (c ω)⁻¹ * c ω'
    have hψc : Continuous ψ := by
      change Continuous fun a => (c ω a)⁻¹ * c ω' a
      exact ((hccont ω).inv).mul (hccont ω')
    have hψn : ∀ a, ‖(ψ a : ℂ)‖ = 1 := by
      intro a
      change ‖(((c ω a)⁻¹ * c ω' a : ℂˣ) : ℂ)‖ = 1
      rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hcnorm, hcnorm, inv_one,
        one_mul]
    have hψK : ∀ a : A, (a : G) ∈ commonNormKernel ν → ψ a = 1 := fun a ha => hR a ha
    obtain ⟨η, hη, hηa⟩ := hsurj ψ hψc hψn hψK
    refine ⟨⟨η, hη⟩, ?_⟩
    have h := classActsByCharacter_twist η.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν ⟨η, hη.1⟩) (hcacts ω)
    have hchar : η.toMonoidHom.comp A.subtype * c ω = c ω' := by
      ext a : 1
      change η a * c ω a = c ω' a
      rw [hηa a]
      change (c ω a)⁻¹ * c ω' a * c ω a = c ω' a
      rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hchar] at h
    exact h
  · -- the central characters have finitely many classes modulo `Im X(G)`
    refine (finite_image_mk_characterAnnihilator K U hK hU).subset ?_
    rintro _ ⟨_, ⟨ω, hω, rfl⟩, rfl⟩
    exact ⟨c ω, fun u hu => classActsByCharacter_eq_one (hcacts ω) hω u hu, rfl⟩
  · -- the fibres are finite
    intro ω hω
    refine (hfin (c ω) (hccont ω) (hcnorm ω)
      (fun a ha => classActsByCharacter_eq_one (hcacts ω) hω a ha)).subset ?_
    rintro ω' ⟨hP, hrel⟩
    exact ⟨hrel, hP⟩

/-- **Theorem VIII.1.2 from Proposition VIII.4.1 and Theorem VIII.4.2** (Waldspurger, VIII.5,
printed pp. 331–332), with the hypotheses of `finite_discreteSeriesFixedOrbits` on `A`, `G¹` and
`Im X(G)`: if for every continuous unitary character `χ` of `A` trivial on `A ∩ H` the
`H`-bi-invariant coefficients of all `ω ∈ E₂(G)^H_χ` lie in one finite-dimensional space
(Waldspurger's `p_χ(°C_H)`), then `Θ^H_G` is finite. -/
theorem finite_discreteSeriesFixedOrbits_of_coefficient_mem (H : OpenSubgroup G)
    (hH : IsCompact (H : Set G)) (hH1 : H.toSubgroup ≤ commonNormKernel ν)
    (hA1 : IsCompact ((A ⊓ commonNormKernel ν : Subgroup G) : Set G))
    (hsurj : ∀ χ : A →* ℂˣ, Continuous χ → (∀ a, ‖(χ a : ℂ)‖ = 1) →
      (∀ a : A, (a : G) ∈ commonNormKernel ν → χ a = 1) →
      ∃ η ∈ unitaryUnramifiedCharacters ν, ∀ a : A, η a = χ a)
    (hF : ∀ χ : A →* ℂˣ, Continuous χ → (∀ a, ‖(χ a : ℂ)‖ = 1) →
      (∀ a : A, (a : G) ∈ H → χ a = 1) →
      ∃ F : Submodule ℂ (G → ℂ), FiniteDimensional ℂ F ∧
        ∀ ω ∈ discreteSeriesCentralFixed.{uG, uV} A hA μ χ H.toSubgroup,
          ∀ f ∈ coefficientFunctionSpace ω.val.out.obj, IsBiInvariant H.toSubgroup f → f ∈ F) :
    (discreteSeriesFixedOrbits.{uG, uV} A hA μ ν H.toSubgroup).Finite := by
  refine finite_discreteSeriesFixedOrbits A hA μ ν H.toSubgroup H.isOpen hH1 hA1 hsurj ?_
  intro χ hχc hχn hχH
  obtain ⟨F, hFd, hFm⟩ := hF χ hχc hχn hχH
  have := hFd
  exact finite_discreteSeriesCentralFixed_of_coefficient_mem A hA μ χ H hH F hFm

end Orbits

end Langlands.HarishChandraSchwartz
