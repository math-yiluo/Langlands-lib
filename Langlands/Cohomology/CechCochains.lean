import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

/-!
# Ordered Čech cochains of abelian presheaves

For a presheaf `P` of abelian groups on a topological space `T` and a family `U : ι → Opens T`,
the ordered Čech cochains in degree `p` are the families of sections
`z σ ∈ P(U (σ 0) ⊓ ⋯ ⊓ U (σ p))` indexed by all maps `σ : Fin (p + 1) → ι`.
They form a cosimplicial abelian group, whose alternating coface complex is the ordered Čech
complex. This file records the elementwise differential, functoriality in `P`, and the
long-exact-sequence step that transfers exactness along a sectionwise short exact sequence.
-/

universe w v u

open CategoryTheory Opposite TopologicalSpace

namespace Langlands.Cohomology.Cech

variable {T : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{v} T) {ι : Type w}
  (U : ι → Opens T)

/-- The intersection `U (σ 0) ⊓ ⋯ ⊓ U (σ (n - 1))` of a finite tuple of members of `U`. -/
def inter {n : ℕ} (σ : Fin n → ι) : Opens T := ⨅ a, U (σ a)

variable {U} in
lemma inter_le_comp {m n : ℕ} (σ : Fin n → ι) (θ : Fin m → Fin n) :
    inter U σ ≤ inter U (σ ∘ θ) :=
  le_iInf fun a => iInf_le (fun b => U (σ b)) (θ a)

variable {U} in
lemma inter_le_apply {n : ℕ} (σ : Fin n → ι) (a : Fin n) : inter U σ ≤ U (σ a) :=
  iInf_le (fun b => U (σ b)) a

variable {P} in
/-- Restriction of sections of `P` along an inclusion of opens. -/
def res {V W : Opens T} (h : V ≤ W) : P.obj (op W) →+ P.obj (op V) :=
  (P.map (homOfLE h).op).hom

variable {P} in
@[simp]
lemma res_res {V W W' : Opens T} (h₁ : V ≤ W) (h₂ : W ≤ W') (x : P.obj (op W')) :
    res h₁ (res h₂ x) = res (h₁.trans h₂) x := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

variable {P} in
@[simp]
lemma res_self {V : Opens T} (h : V ≤ V) (x : P.obj (op V)) : res h x = x := by
  simp only [res]
  change (P.map (𝟙 (op V))).hom x = x
  rw [P.map_id]
  rfl

/-- Ordered Čech `p`-cochains of `P` for the family `U`. -/
abbrev C (p : ℕ) : Type (max w v) := ∀ σ : Fin (p + 1) → ι, P.obj (op (inter U σ))

/-- The cosimplicial abelian group of ordered Čech cochains. -/
noncomputable def cosimplicial : CosimplicialObject AddCommGrpCat.{max w v} where
  obj n := AddCommGrpCat.of (∀ σ : Fin (n.len + 1) → ι, P.obj (op (inter U σ)))
  map {m n} θ := AddCommGrpCat.ofHom
    { toFun := fun z τ => res (inter_le_comp τ θ.toOrderHom) (z (τ ∘ θ.toOrderHom))
      map_zero' := by
        funext τ
        exact map_zero _
      map_add' := fun z z' => by
        funext τ
        exact map_add _ _ _ }
  map_id n := by
    ext z τ
    exact res_self _ _
  map_comp {l m n} θ θ' := by
    ext z τ
    exact (res_res _ _ _).symm

/-- The ordered Čech complex of `P` for the family `U`. -/
noncomputable def complex : CochainComplex AddCommGrpCat.{max w v} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (cosimplicial P U)

/-- The Čech differential on `p`-cochains. -/
noncomputable def d (p : ℕ) : C P U p →+ C P U (p + 1) :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimplicial P U) p).hom

/-- The `k`-th coface map on Čech cochains, omitting the `k`-th index. -/
def coface (p : ℕ) (k : Fin (p + 2)) : C P U p →+ C P U (p + 1) where
  toFun z τ := res (inter_le_comp τ k.succAbove) (z (τ ∘ k.succAbove))
  map_zero' := by
    funext τ
    exact map_zero _
  map_add' z z' := by
    funext τ
    exact map_add _ _ _

lemma d_eq_sum (p : ℕ) :
    d P U p = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • coface P U p k := by
  have h := map_sum AddCommGrpCat.homAddEquiv
    (fun k : Fin (p + 2) => (-1 : ℤ) ^ (k : ℕ) • (cosimplicial P U).δ k) Finset.univ
  simp only [map_zsmul] at h
  exact h

lemma d_apply (p : ℕ) (z : C P U p) (τ : Fin (p + 2) → ι) :
    d P U p z τ = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
      res (inter_le_comp τ k.succAbove) (z (τ ∘ k.succAbove)) := by
  rw [d_eq_sum, AddMonoidHom.finsetSum_apply, Finset.sum_apply]
  rfl

lemma d_d (p : ℕ) (z : C P U p) : d P U (p + 1) (d P U p z) = 0 := by
  have h := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (cosimplicial P U) p
  exact congrArg (fun f => f.hom z) h

/-- The ordered Čech complex is exact in degree `p + 1`: every `(p + 1)`-cocycle is a
coboundary. -/
def ExactAt (p : ℕ) : Prop :=
  ∀ z : C P U (p + 1), d P U (p + 1) z = 0 → ∃ y : C P U p, d P U p y = z

variable {P} in
/-- The map of Čech cochains induced by a morphism of presheaves. -/
def map {Q : TopCat.Presheaf AddCommGrpCat.{v} T} (φ : P ⟶ Q) (p : ℕ) : C P U p →+ C Q U p where
  toFun z σ := φ.app _ (z σ)
  map_zero' := by
    funext σ
    exact map_zero _
  map_add' z z' := by
    funext σ
    exact map_add _ _ _

variable {P} in
lemma map_res {Q : TopCat.Presheaf AddCommGrpCat.{v} T} (φ : P ⟶ Q) {V W : Opens T}
    (h : V ≤ W) (x : P.obj (op W)) : φ.app (op V) (res h x) = res h (φ.app (op W) x) := by
  simp only [res, ← ConcreteCategory.comp_apply]
  rw [φ.naturality]

variable {P} in
lemma d_map {Q : TopCat.Presheaf AddCommGrpCat.{v} T} (φ : P ⟶ Q) (p : ℕ) (z : C P U p) :
    d Q U p (map U φ p z) = map U φ (p + 1) (d P U p z) := by
  funext τ
  simp only [d_apply, map, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, map_zsmul, map_res]

/-- Sections of a family of cochains at equal indices agree after restriction to a common
smaller open. -/
lemma res_congr {n : ℕ} {σ σ' : Fin n → ι} (h : σ = σ')
    (x : ∀ σ : Fin n → ι, P.obj (op (inter U σ))) {V : Opens T} (hV : V ≤ inter U σ)
    (hV' : V ≤ inter U σ') : res hV (x σ) = res hV' (x σ') := by
  subst h
  rfl

lemma inter_cons {n : ℕ} (i : ι) (σ : Fin n → ι) :
    inter U (Fin.cons i σ : Fin (n + 1) → ι) = U i ⊓ inter U σ := by
  apply le_antisymm
  · refine le_inf ?_ (le_iInf fun a => ?_)
    · simpa using inter_le_apply (U := U) (Fin.cons i σ : Fin (n + 1) → ι) 0
    · simpa using inter_le_apply (U := U) (Fin.cons i σ : Fin (n + 1) → ι) a.succ
  · refine le_iInf (Fin.cases ?_ fun a => ?_)
    · simp
    · simpa using inf_le_right.trans (inter_le_apply (U := U) σ a)

lemma cons_comp_succAbove_zero {n : ℕ} (i : ι) (τ : Fin (n + 1) → ι) :
    (Fin.cons i τ : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = τ := by
  funext a
  simp

lemma cons_comp_succAbove_succ {n : ℕ} (i : ι) (τ : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons i τ : Fin (n + 2) → ι) ∘ k.succ.succAbove =
      (Fin.cons i (τ ∘ k.succAbove) : Fin (n + 1) → ι) := by
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · simp
  · simp

variable {U} in
lemma le_inter_cons_comp {n : ℕ} (i : ι) (τ : Fin (n + 1) → ι) (k : Fin (n + 1))
    {O : Opens T} (hO : O ≤ U i ⊓ inter U τ) :
    O ≤ inter U (Fin.cons i (τ ∘ k.succAbove) : Fin (n + 1) → ι) :=
  (hO.trans (inf_le_inf_left _ (inter_le_comp τ k.succAbove))).trans (inter_cons U i _).ge

variable {P U} in
/-- The cocycle condition at `Fin.cons i τ`, restricted to an open contained in `U i ⊓ U_τ`:
the restriction of `z τ` is the alternating sum of the restrictions of the
`z (i, τ₀, …, τ̂ₖ, …)`. -/
lemma res_eq_sum_of_d_eq_zero {p : ℕ} {z : C P U (p + 1)} (hz : d P U (p + 1) z = 0) (i : ι)
    (τ : Fin (p + 2) → ι) {O : Opens T} (hO : O ≤ U i ⊓ inter U τ) :
    res (hO.trans inf_le_right) (z τ) = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
      res (le_inter_cons_comp i τ k hO) (z (Fin.cons i (τ ∘ k.succAbove))) := by
  have hO' : O ≤ inter U (Fin.cons i τ : Fin (p + 3) → ι) := hO.trans (inter_cons U i τ).ge
  have h := congrArg (res hO') (congrFun hz (Fin.cons i τ))
  rw [d_apply, map_sum, Pi.zero_apply, map_zero, Fin.sum_univ_succ] at h
  simp only [map_zsmul, map_neg, res_res, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] at h
  rw [res_congr P U (cons_comp_succAbove_zero i τ).symm z _ (hO'.trans (inter_le_comp _ _)), h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [res_congr P U (cons_comp_succAbove_succ i τ k) z]

/-- The long-exact-sequence step: if `0 ⟶ A ⟶ B ⟶ C' ⟶ 0` is exact on sections over every
nonempty finite intersection of the family, the Čech complex of `B` is exact in degree `p + 1`
and that of `A` in degree `p + 2`, then the Čech complex of `C'` is exact in degree `p + 1`. -/
lemma exactAt_of_shortExact {A B C' : TopCat.Presheaf AddCommGrpCat.{v} T} (i : A ⟶ B)
    (π : B ⟶ C')
    (hiπ : ∀ (n : ℕ) (σ : Fin (n + 1) → ι) (a : A.obj (op (inter U σ))),
      π.app _ (i.app _ a) = 0)
    (hi : ∀ (n : ℕ) (σ : Fin (n + 1) → ι), Function.Injective (i.app (op (inter U σ))))
    (hex : ∀ (n : ℕ) (σ : Fin (n + 1) → ι) (b : B.obj (op (inter U σ))),
      π.app _ b = 0 → ∃ a, i.app _ a = b)
    (hπ : ∀ (n : ℕ) (σ : Fin (n + 1) → ι), Function.Surjective (π.app (op (inter U σ))))
    {p : ℕ} (hB : ExactAt B U p) (hA : ExactAt A U (p + 1)) : ExactAt C' U p := by
  intro z hz
  choose w hw using fun σ => hπ _ σ (z σ)
  have hdw : ∀ τ, π.app _ (d B U (p + 1) w τ) = 0 := by
    intro τ
    have := congrFun (d_map U π (p + 1) w) τ
    have hwz : map U π (p + 1) w = z := funext hw
    rw [hwz, hz] at this
    exact this.symm
  choose v hv using fun τ => hex _ τ _ (hdw τ)
  have hv' : map U i (p + 2) v = d B U (p + 1) w := funext hv
  have hdv : d A U (p + 2) v = 0 := by
    funext τ
    apply hi _ τ
    have := congrFun (d_map U i (p + 2) v) τ
    rw [hv', d_d] at this
    rw [Pi.zero_apply, map_zero]
    exact this.symm
  obtain ⟨u, hu⟩ := hA v hdv
  obtain ⟨x, hx⟩ := hB (w - map U i (p + 1) u) (by
    rw [map_sub, d_map, hu, hv', sub_self])
  refine ⟨map U π p x, ?_⟩
  rw [d_map, hx]
  funext σ
  have h0 : π.app _ (i.app _ (u σ)) = 0 := hiπ _ σ (u σ)
  simp only [map, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, map_sub, h0, sub_zero, hw]

end Langlands.Cohomology.Cech
