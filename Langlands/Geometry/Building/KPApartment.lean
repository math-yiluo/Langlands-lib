import Langlands.Geometry.Building.RootDatumValuation
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Set.Card

/-!
# The apartment of an equipollence class of valuations of the root datum

For `i : S ⟶ G` (meant: a maximal split torus of a connected reductive group over a field `k`)
and `ω : kˣ → ℝ` (meant: the valuation of `k`), `KPApartmentData i ω` is an `N(k)`-stable
equipollence class `A` of `ω`-compatible valuations of the root datum (KP §6.3, opening
paragraph, and Chapter 7, opening paragraphs). Its points form the reduced apartment
`D.Apartment`, an affine space over `TranslationSpace i`, the quotient of `V(S)` by the common
kernel of the roots, on which the actual normalizer points act by affine automorphisms. On `A` we define the filtration groups `U_{a,x,r}`, the affine root groups `U_ψ`
and `U_{ψ+}` (KP Definition 6.3.1) and the sets `Ψ ⊆ Ψ′` of KP Definition 6.3.4.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

open RootFunctionFamily

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Translations

variable (i : S.toGrp ⟶ G) [IsAffineHom G.X.hom]

/-- The common kernel of the relative roots in `V(S)`. It is the stabilizer of every valuation
(`IsRootDatumValuation.vadd_eq_self_iff`), which KP (after Lemma 6.1.6) identify with
`V(A_G)` for connected reductive `G`; that identification is not made here. -/
abbrev rootAnnihilator : Submodule ℝ (V S) :=
  RealTorusSpace.relativeCentralDirections i

variable {i} in
theorem mem_rootAnnihilator {v : V S} :
    v ∈ rootAnnihilator i ↔ ∀ a ∈ relativeRoots i, eval S a v = 0 := by
  exact RealTorusSpace.mem_relativeCentralDirections i v

/-- The space of translations of the apartment, `V(S)` modulo the common kernel of the roots
(KP's `V(S/A_G) = V(S′)`, §6.1(c); not identified with it here). -/
abbrev TranslationSpace : Type u :=
  V S ⧸ rootAnnihilator i

/-- The linear form on `TranslationSpace i` induced by a relative root. -/
def rootForm (α : relativeRoots i) : TranslationSpace i →ₗ[ℝ] ℝ :=
  (rootAnnihilator i).liftQ (eval S α.1) fun _ hv =>
    LinearMap.mem_ker.2 (mem_rootAnnihilator.1 hv α.1 α.2)

@[simp] theorem rootForm_mk (α : relativeRoots i) (v : V S) :
    rootForm i α (Submodule.Quotient.mk v) = eval S α.1 v :=
  rfl

open Classical in
/-- `U_{2a}(k)`, with the convention `U_{2a}(k) = {1}` if `2a` is not a root (KP, before
Definition 6.3.4). -/
def doubleRootGroupPoints (a : characterLattice S) : Subgroup (rationalPoints G) :=
  if 2 • a ∈ relativeRoots i then rootGroupPoints i (2 • a) else ⊥

variable [Mono i.hom.hom.left]

theorem smul_mem_rootAnnihilator (n : normalizerPoints i) {v : V S}
    (hv : v ∈ rootAnnihilator i) : n • v ∈ rootAnnihilator i := by
  rw [mem_rootAnnihilator] at hv ⊢
  intro a ha
  rw [eval_normalizer_smul]
  exact hv _ (weylAction_mapsTo_relativeRoots i n⁻¹ ha)

theorem map_normalizerAction_rootAnnihilator (n : normalizerPoints i) :
    (rootAnnihilator i).map (normalizerAction i n : V S →ₗ[ℝ] V S) = rootAnnihilator i := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact smul_mem_rootAnnihilator i n hv
  · intro v hv
    refine ⟨n⁻¹ • v, smul_mem_rootAnnihilator i n⁻¹ hv, ?_⟩
    change n • (n⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel, one_smul]

/-- The linear action of the normalizer points on `TranslationSpace i`, induced by the
published action `normalizerAction i` on `V(S)`. -/
def translationAction :
    normalizerPoints i →* (TranslationSpace i ≃ₗ[ℝ] TranslationSpace i) where
  toFun n := Submodule.Quotient.equiv _ _ (normalizerAction i n)
    (map_normalizerAction_rootAnnihilator i n)
  map_one' := by
    refine LinearEquiv.ext fun v => Submodule.Quotient.induction_on _ v fun v => ?_
    change Submodule.Quotient.mk (normalizerAction i 1 v) = Submodule.Quotient.mk v
    rw [map_one, LinearEquiv.coe_one, id]
  map_mul' n m := by
    refine LinearEquiv.ext fun v => Submodule.Quotient.induction_on _ v fun v => ?_
    change Submodule.Quotient.mk (normalizerAction i (n * m) v) =
      Submodule.Quotient.mk (normalizerAction i n (normalizerAction i m v))
    rw [map_mul, LinearEquiv.mul_apply]

@[simp] theorem translationAction_mk (n : normalizerPoints i) (v : V S) :
    translationAction i n (Submodule.Quotient.mk v) = Submodule.Quotient.mk (n • v) :=
  rfl

end Translations

section Valuations

variable {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {φ : RootFunctionFamily S G}

namespace IsRootDatumValuation

/-- By V 0, a valuation takes a finite value on each root group. -/
theorem exists_ne_top (h : IsRootDatumValuation i φ) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) : ∃ u ∈ rootGroupPoints i a, φ a u ≠ ⊤ := by
  by_contra! hcon
  have hsub : φ a '' (rootGroupPoints i a : Set (rationalPoints G)) ⊆ {⊤} := by
    rintro _ ⟨u, hu, rfl⟩
    exact hcon u hu
  have h1 := (Set.encard_le_encard hsub).trans_eq (Set.encard_singleton ⊤)
  have h3 : (3 : ℕ∞) ≤ 1 := (h.three_le_encard a ha).trans h1
  norm_num at h3

/-- The stabilizer of a valuation in `V(S)` is the common kernel of the roots
(KP, after Lemma 6.1.6). -/
theorem vadd_eq_self_iff (h : IsRootDatumValuation i φ) {v : V S} :
    v +ᵥ φ = φ ↔ v ∈ rootAnnihilator i := by
  constructor
  · intro hv
    rw [mem_rootAnnihilator]
    intro a ha
    obtain ⟨u, -, hne⟩ := h.exists_ne_top ha
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
    have hval := congrArg (fun ψ : RootFunctionFamily S G => ψ a u) hv
    simp only [vadd_apply, ← ht] at hval
    rw [← WithTop.coe_add, WithTop.coe_inj] at hval
    linarith
  · intro hv
    ext a g
    rw [vadd_apply]
    by_cases ha : a ∈ relativeRoots i
    · rw [mem_rootAnnihilator.1 hv a ha, WithTop.coe_zero, add_zero]
    · rw [h.eq_top_of_not_mem_roots a ha g, WithTop.top_add]

theorem vadd_eq_vadd_iff (h : IsRootDatumValuation i φ) {v w : V S} :
    v +ᵥ φ = w +ᵥ φ ↔ v - w ∈ rootAnnihilator i := by
  rw [← h.vadd_eq_self_iff]
  constructor
  · intro hvw
    calc (v - w) +ᵥ φ = -w +ᵥ (v +ᵥ φ) := by rw [vadd_vadd, neg_add_eq_sub]
      _ = -w +ᵥ (w +ᵥ φ) := by rw [hvw]
      _ = φ := by rw [vadd_vadd, neg_add_cancel, zero_vadd]
  · intro h0
    calc v +ᵥ φ = w +ᵥ ((v - w) +ᵥ φ) := by rw [vadd_vadd, add_sub_cancel]
      _ = w +ᵥ φ := by rw [h0]

/-- For a valuation, `U_{a,φ,r}` is a subgroup for every character `a`; for `a ∉ Φ` it is
`U_a(k)`. -/
def filtrationSubgroup (h : IsRootDatumValuation i φ) (a : characterLattice S) (r : ℝ) :
    Subgroup (rationalPoints G) where
  carrier := rootFiltration i φ a r
  one_mem' := by
    by_cases ha : a ∈ relativeRoots i
    · exact h.one_mem a ha r
    · exact ⟨(rootGroupPoints i a).one_mem, by
        rw [h.eq_top_of_not_mem_roots a ha]
        exact le_top⟩
  mul_mem' {g g'} hg hg' := by
    by_cases ha : a ∈ relativeRoots i
    · exact h.mul_mem a ha r g g' hg hg'
    · exact ⟨(rootGroupPoints i a).mul_mem hg.1 hg'.1, by
        rw [h.eq_top_of_not_mem_roots a ha]
        exact le_top⟩
  inv_mem' {g} hg := by
    by_cases ha : a ∈ relativeRoots i
    · exact h.inv_mem a ha r g hg
    · exact ⟨(rootGroupPoints i a).inv_mem hg.1, by
        rw [h.eq_top_of_not_mem_roots a ha]
        exact le_top⟩

theorem coe_filtrationSubgroup (h : IsRootDatumValuation i φ) (a : characterLattice S)
    (r : ℝ) : (h.filtrationSubgroup a r : Set (rationalPoints G)) = rootFiltration i φ a r :=
  rfl

theorem filtrationSubgroup_antitone (h : IsRootDatumValuation i φ) (a : characterLattice S) :
    Antitone (h.filtrationSubgroup a) :=
  fun _ _ hrs _ hg => ⟨hg.1, (WithTop.coe_le_coe.2 hrs).trans hg.2⟩

end IsRootDatumValuation

end Valuations

variable (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- Valid apartment data for `(G, S)`: an equipollence class `A` of valuations of the root datum
which are compatible with `ω` on `S(k)` (the `S(k)`-part of KP axiom V 6), and which is stable
under the normalizer points `N(k)`. This is the hypothesis on `A(S)` of KP Chapter 7 (opening
paragraphs), with V 6 only on `S(k)`; for the canonical class of a quasi-split group,
`N(k)`-stability is KP Lemma 6.1.28. That such data exist for a given `G` is a separate
statement, not asserted here. -/
structure KPApartmentData (ω : kˣ → ℝ) where
  /-- The equipollence class `A`. -/
  carrier : Set (RootFunctionFamily S G)
  /-- `A` is the `V(S)`-orbit of an `ω`-compatible valuation of the root datum. -/
  exists_eq_orbit : ∃ φ, IsRootDatumValuation i φ ∧ IsSplitTorusCompatible i ω φ ∧
    carrier = AddAction.orbit (V S) φ
  /-- `A` is stable under the action of `N(k)` (KP 6.1.8). -/
  smul_mem : ∀ n : normalizerPoints i, ∀ φ ∈ carrier, n • φ ∈ carrier

namespace KPApartmentData

variable {i} {ω : kˣ → ℝ} (D : KPApartmentData i ω)

theorem isRootDatumValuation_of_mem {φ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier) :
    IsRootDatumValuation i φ := by
  obtain ⟨φ₀, h₀, -, hc⟩ := D.exists_eq_orbit
  rw [hc] at hφ
  obtain ⟨v, rfl⟩ := hφ
  exact h₀.vadd v

theorem isSplitTorusCompatible_of_mem {φ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier) :
    IsSplitTorusCompatible i ω φ := by
  obtain ⟨φ₀, -, h₀, hc⟩ := D.exists_eq_orbit
  rw [hc] at hφ
  obtain ⟨v, rfl⟩ := hφ
  exact h₀.vadd i v

theorem vadd_mem {φ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier) (v : V S) :
    v +ᵥ φ ∈ D.carrier := by
  obtain ⟨φ₀, -, -, hc⟩ := D.exists_eq_orbit
  rw [hc] at hφ ⊢
  obtain ⟨w, rfl⟩ := hφ
  exact ⟨v + w, add_vadd v w φ₀⟩

theorem equipollent_of_mem {φ ψ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier)
    (hψ : ψ ∈ D.carrier) : Equipollent φ ψ := by
  obtain ⟨φ₀, -, -, hc⟩ := D.exists_eq_orbit
  rw [hc] at hφ hψ
  obtain ⟨v, rfl⟩ := hφ
  obtain ⟨w, rfl⟩ := hψ
  exact ⟨w - v, by rw [vadd_vadd, sub_add_cancel]⟩

/-- `A` is a full equipollence class. -/
theorem mem_iff_equipollent {φ ψ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier) :
    ψ ∈ D.carrier ↔ Equipollent φ ψ :=
  ⟨D.equipollent_of_mem hφ, fun ⟨v, hv⟩ => hv ▸ D.vadd_mem hφ v⟩

/-- The points of the (reduced) apartment: the valuations of the class `A`
(KP §6.3, opening paragraph, and Definition 6.1.24). -/
@[ext] structure Apartment where
  /-- The valuation of the root datum which is this point. -/
  val : RootFunctionFamily S G
  mem : val ∈ D.carrier

variable {D}

theorem Apartment.isValuation (x : D.Apartment) : IsRootDatumValuation i x.val :=
  D.isRootDatumValuation_of_mem x.mem

theorem Apartment.isSplitTorusCompatible (x : D.Apartment) :
    IsSplitTorusCompatible i ω x.val :=
  D.isSplitTorusCompatible_of_mem x.mem

instance : Nonempty D.Apartment := by
  obtain ⟨φ, -, -, hc⟩ := D.exists_eq_orbit
  exact ⟨⟨φ, hc ▸ AddAction.mem_orbit_self φ⟩⟩

/-! ### The affine structure -/

instance : VAdd (TranslationSpace i) D.Apartment where
  vadd v x := Quotient.liftOn' v (fun w => (⟨w +ᵥ x.val, D.vadd_mem x.mem w⟩ : D.Apartment))
    fun _ _ hww' => Apartment.ext
      (x.isValuation.vadd_eq_vadd_iff.2 ((Submodule.quotientRel_def _).1 hww'))

@[simp] theorem val_mk_vadd (w : V S) (x : D.Apartment) :
    ((Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x).val = w +ᵥ x.val :=
  rfl

instance : VSub (TranslationSpace i) D.Apartment where
  vsub x y := Submodule.Quotient.mk (Classical.choose (D.equipollent_of_mem y.mem x.mem))

theorem vsub_def (x y : D.Apartment) :
    x -ᵥ y = Submodule.Quotient.mk (Classical.choose (D.equipollent_of_mem y.mem x.mem)) :=
  rfl

/-- The apartment is an affine space over `TranslationSpace i` (KP Lemma 6.1.6 and the remark
after it: the stabilizer of every valuation is the kernel of the action). -/
instance : AddTorsor (TranslationSpace i) D.Apartment where
  zero_vadd x := Apartment.ext (zero_vadd (V S) x.val)
  add_vadd v w x :=
    Submodule.Quotient.induction_on _ v fun v => Submodule.Quotient.induction_on _ w fun w =>
      Apartment.ext (add_vadd v w x.val)
  vsub_vadd' x y := Apartment.ext (Classical.choose_spec (D.equipollent_of_mem y.mem x.mem)).symm
  vadd_vsub' v x := Submodule.Quotient.induction_on _ v fun w => by
    rw [vsub_def, Submodule.Quotient.eq]
    have hspec := Classical.choose_spec (D.equipollent_of_mem x.mem
      ((Submodule.Quotient.mk w : TranslationSpace i) +ᵥ x).mem)
    exact x.isValuation.vadd_eq_vadd_iff.1 hspec.symm

theorem vsub_eq_mk {x y : D.Apartment} {w : V S} (h : x.val = w +ᵥ y.val) :
    x -ᵥ y = Submodule.Quotient.mk w :=
  (eq_vadd_iff_vsub_eq x _ y).1 (Apartment.ext h)

/-! ### The action of the normalizer points (KP 6.1.8) -/

instance : MulAction (normalizerPoints i) D.Apartment where
  smul n x := ⟨n • x.val, D.smul_mem n _ x.mem⟩
  one_smul x := Apartment.ext (one_smul _ x.val)
  mul_smul n m x := Apartment.ext (mul_smul n m x.val)

@[simp] theorem val_smul (n : normalizerPoints i) (x : D.Apartment) : (n • x).val = n • x.val :=
  rfl

/-- `n(x + v) = nx + n·v` (KP 6.1.8, corrected Lemma 6.1.12). -/
theorem smul_vadd (n : normalizerPoints i) (v : TranslationSpace i) (x : D.Apartment) :
    n • (v +ᵥ x) = translationAction i n v +ᵥ n • x :=
  Submodule.Quotient.induction_on _ v fun w => by
    rw [translationAction_mk]
    exact Apartment.ext (RootFunctionFamily.smul_vadd n w x.val)

variable (D) in
/-- The actual normalizer points act on the apartment by affine automorphisms whose linear
parts are `translationAction i`. -/
def normalizerAffineEquiv : normalizerPoints i →* (D.Apartment ≃ᵃ[ℝ] D.Apartment) where
  toFun n :=
    { toFun := fun x => n • x
      invFun := fun x => n⁻¹ • x
      left_inv := fun x => inv_smul_smul n x
      right_inv := fun x => smul_inv_smul n x
      linear := translationAction i n
      map_vadd' := fun x v => smul_vadd n v x }
  map_one' := AffineEquiv.ext fun x => one_smul (normalizerPoints i) x
  map_mul' n m := AffineEquiv.ext fun x => mul_smul n m x

@[simp] theorem normalizerAffineEquiv_apply (n : normalizerPoints i) (x : D.Apartment) :
    D.normalizerAffineEquiv n x = n • x :=
  rfl

/-! ### Filtration groups and affine root groups -/

variable (D) in
/-- The filtration group `U_{a,x,r}` of the point `x ∈ A` (KP Definition 6.1.2, V 1); for a
character `a` that is not a root it is `U_a(k)`. -/
def filtration (x : D.Apartment) (a : characterLattice S) (r : ℝ) :
    Subgroup (rationalPoints G) :=
  x.isValuation.filtrationSubgroup a r

theorem mem_filtration {x : D.Apartment} {a : characterLattice S} {r : ℝ}
    {g : rationalPoints G} :
    g ∈ D.filtration x a r ↔ g ∈ rootGroupPoints i a ∧ (r : WithTop ℝ) ≤ x.val a g :=
  Iff.rfl

theorem filtration_le_rootGroupPoints (x : D.Apartment) (a : characterLattice S) (r : ℝ) :
    D.filtration x a r ≤ rootGroupPoints i a :=
  fun _ hg => hg.1

theorem filtration_antitone (x : D.Apartment) (a : characterLattice S) :
    Antitone (D.filtration x a) :=
  x.isValuation.filtrationSubgroup_antitone a

/-- `U_{a,x+v,r} = U_{a,x,r-a(v)}` (KP Lemma 6.1.6). -/
theorem filtration_vadd (x : D.Apartment) (v : TranslationSpace i) (α : relativeRoots i)
    (r : ℝ) : D.filtration (v +ᵥ x) α r = D.filtration x α (r - rootForm i α v) :=
  Submodule.Quotient.induction_on _ v fun w =>
    SetLike.ext' (rootFiltration_vadd' x.val w α.1 r)

variable (D) in
/-- The affine root group `U_ψ = U_{a,x,ψ(x)}` of an affine functional `ψ` with derivative
`a` (KP Definition 6.3.1), written as the intersection over all points `x ∈ A`; see
`affineRootGroup_eq_filtration` for independence of `x`. -/
def affineRootGroup (a : characterLattice S) (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    Subgroup (rationalPoints G) :=
  ⨅ x : D.Apartment, D.filtration x a (ψ x)

/-- If `ψ` has derivative `a`, then `U_ψ = U_{a,x,ψ(x)}` for every `x ∈ A`
(KP Definition 6.3.1). -/
theorem affineRootGroup_eq_filtration {α : relativeRoots i} {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ.linear = rootForm i α) (x : D.Apartment) :
    D.affineRootGroup α ψ = D.filtration x α (ψ x) := by
  have key : ∀ y, D.filtration y α (ψ y) = D.filtration x α (ψ x) := by
    intro y
    obtain ⟨v, rfl⟩ : ∃ v, y = v +ᵥ x := ⟨y -ᵥ x, (vsub_vadd y x).symm⟩
    rw [filtration_vadd, AffineMap.map_vadd, hψ, vadd_eq_add, add_sub_cancel_left]
  simp only [affineRootGroup, key, iInf_const]

/-- `U_ψ = {u ∈ U_a(k) | x_a(u) ≥ ψ(x)}` for any `x ∈ A` (KP Remark 6.3.2). -/
theorem mem_affineRootGroup_iff {α : relativeRoots i} {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ.linear = rootForm i α) (x : D.Apartment) {u : rationalPoints G} :
    u ∈ D.affineRootGroup α ψ ↔
      u ∈ rootGroupPoints i α ∧ ((ψ x : ℝ) : WithTop ℝ) ≤ x.val α u := by
  rw [affineRootGroup_eq_filtration hψ x]
  rfl

theorem affineRootGroup_le_rootGroupPoints (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) : D.affineRootGroup a ψ ≤ rootGroupPoints i a := by
  obtain ⟨x⟩ := (inferInstance : Nonempty D.Apartment)
  exact (iInf_le _ x).trans (filtration_le_rootGroupPoints x a _)

theorem affineRootGroup_add_const_antitone (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    Antitone fun c : ℝ => D.affineRootGroup a (ψ + AffineMap.const ℝ D.Apartment c) := by
  intro c c' hcc'
  refine iInf_mono fun x => filtration_antitone x a ?_
  simp only [AffineMap.coe_add, Pi.add_apply, AffineMap.coe_const, Function.const_apply]
  linarith

variable (D) in
/-- `U_{ψ+} = ⋃_{ψ' > ψ} U_{ψ'}` (KP Definition 6.3.1). An affine functional `ψ' > ψ` with the
same derivative is `ψ + c` for a constant `c > 0`. The union is directed, so it is the
subgroup supremum. -/
def affineRootGroupPlus (a : characterLattice S) (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    Subgroup (rationalPoints G) :=
  ⨆ c : Set.Ioi (0 : ℝ), D.affineRootGroup a (ψ + AffineMap.const ℝ D.Apartment (c : ℝ))

theorem mem_affineRootGroupPlus {a : characterLattice S} {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    {u : rationalPoints G} :
    u ∈ D.affineRootGroupPlus a ψ ↔
      ∃ c : ℝ, 0 < c ∧ u ∈ D.affineRootGroup a (ψ + AffineMap.const ℝ D.Apartment c) := by
  have : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, Set.mem_Ioi.2 one_pos⟩⟩
  rw [affineRootGroupPlus, Subgroup.mem_iSup_of_directed]
  · exact ⟨fun ⟨c, hc⟩ => ⟨c, c.2, hc⟩, fun ⟨c, hc, hu⟩ => ⟨⟨c, hc⟩, hu⟩⟩
  · intro c c'
    refine ⟨⟨min c c', Set.mem_Ioi.2 (lt_min c.2 c'.2)⟩, ?_, ?_⟩
    · exact affineRootGroup_add_const_antitone a ψ (min_le_left _ _)
    · exact affineRootGroup_add_const_antitone a ψ (min_le_right _ _)

theorem affineRootGroupPlus_le (a : characterLattice S) (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    D.affineRootGroupPlus a ψ ≤ D.affineRootGroup a ψ := by
  intro u hu
  obtain ⟨c, hc, hu⟩ := mem_affineRootGroupPlus.1 hu
  have hle := affineRootGroup_add_const_antitone a ψ hc.le hu
  have h0 : ψ + AffineMap.const ℝ D.Apartment (0 : ℝ) = ψ := by
    ext
    simp
  simpa only [h0] using hle

/-- `U_{ψ+} = {u ∈ U_a(k) | x_a(u) > ψ(x)}` for any `x ∈ A`. -/
theorem mem_affineRootGroupPlus_iff {α : relativeRoots i} {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ.linear = rootForm i α) (x : D.Apartment) {u : rationalPoints G} :
    u ∈ D.affineRootGroupPlus α ψ ↔
      u ∈ rootGroupPoints i α ∧ ((ψ x : ℝ) : WithTop ℝ) < x.val α u := by
  have hlin : ∀ c : ℝ, (ψ + AffineMap.const ℝ D.Apartment c).linear = rootForm i α := by
    intro c
    rw [AffineMap.add_linear, AffineMap.const_linear, add_zero, hψ]
  have happ : ∀ c : ℝ, (ψ + AffineMap.const ℝ D.Apartment c) x = ψ x + c := fun c => rfl
  rw [mem_affineRootGroupPlus]
  constructor
  · rintro ⟨c, hc, hu⟩
    rw [mem_affineRootGroup_iff (hlin c) x, happ] at hu
    exact ⟨hu.1, lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by linarith)) hu.2⟩
  · rintro ⟨hu, hlt⟩
    induction h : x.val α u using WithTop.recTopCoe with
    | top =>
      refine ⟨1, one_pos, (mem_affineRootGroup_iff (hlin 1) x).2 ⟨hu, ?_⟩⟩
      rw [h]
      exact le_top
    | coe t =>
      rw [h, WithTop.coe_lt_coe] at hlt
      refine ⟨t - ψ x, sub_pos.2 hlt, (mem_affineRootGroup_iff (hlin _) x).2 ⟨hu, ?_⟩⟩
      rw [h, happ, add_sub_cancel]

/-! ### Affine roots (KP Definition 6.3.4) -/

variable (D) in
/-- The set `Ψ′` of affine functionals `ψ` with derivative a root `a` such that
`U_{ψ+} ≠ U_ψ` (KP Definition 6.3.4). -/
def extendedAffineRoots : Set (D.Apartment →ᵃ[ℝ] ℝ) :=
  {ψ | ∃ α : relativeRoots i, ψ.linear = rootForm i α ∧
    D.affineRootGroupPlus α ψ ≠ D.affineRootGroup α ψ}

variable (D) in
/-- The affine root system `Ψ` of `G` with respect to `S`: affine functionals `ψ` with
derivative a root `a` such that `U_ψ ⊈ U_{ψ+} · U_{2a}(k)` (KP Definition 6.3.4). -/
def affineRoots : Set (D.Apartment →ᵃ[ℝ] ℝ) :=
  {ψ | ∃ α : relativeRoots i, ψ.linear = rootForm i α ∧
    ¬ (D.affineRootGroup α ψ : Set (rationalPoints G)) ⊆
      (D.affineRootGroupPlus α ψ : Set (rationalPoints G)) *
        (doubleRootGroupPoints i α : Set (rationalPoints G))}

/-- `Ψ ⊆ Ψ′` (KP, after Remark 6.3.5). -/
theorem affineRoots_subset_extendedAffineRoots : D.affineRoots ⊆ D.extendedAffineRoots := by
  rintro ψ ⟨α, hψ, hnot⟩
  refine ⟨α, hψ, fun heq => hnot fun u hu => ?_⟩
  refine ⟨u, ?_, 1, (doubleRootGroupPoints i α).one_mem, mul_one u⟩
  rw [heq]
  exact hu

/-! ### Affine functionals from triples `(a, x, r)` -/

variable (D) in
/-- The unique affine functional with derivative `a` and value `r` at `x` (KP, after
Definition 6.3.1). -/
def affineFunctional (α : relativeRoots i) (x : D.Apartment) (r : ℝ) :
    D.Apartment →ᵃ[ℝ] ℝ :=
  AffineMap.mk' (fun y => rootForm i α (y -ᵥ x) + r) (rootForm i α) x fun y => by
    rw [vsub_self, map_zero, zero_add, vadd_eq_add]

@[simp] theorem affineFunctional_apply (α : relativeRoots i) (x y : D.Apartment) (r : ℝ) :
    D.affineFunctional α x r y = rootForm i α (y -ᵥ x) + r :=
  rfl

@[simp] theorem affineFunctional_linear (α : relativeRoots i) (x : D.Apartment) (r : ℝ) :
    (D.affineFunctional α x r).linear = rootForm i α :=
  rfl

/-- The two indexings of filtration groups agree: `U_{a,x,r} = U_ψ` for the affine functional
`ψ` with derivative `a` and `ψ(x) = r` (KP, after Definition 6.3.1). -/
theorem filtration_eq_affineRootGroup (α : relativeRoots i) (x : D.Apartment) (r : ℝ) :
    D.filtration x α r = D.affineRootGroup α (D.affineFunctional α x r) := by
  rw [affineRootGroup_eq_filtration (affineFunctional_linear α x r) x, affineFunctional_apply,
    vsub_self, map_zero, zero_add]

end KPApartmentData

end Langlands.Geometry.Building
