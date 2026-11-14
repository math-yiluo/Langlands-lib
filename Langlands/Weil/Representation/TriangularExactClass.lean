import Langlands.VirtualRepresentation.Weil.ExactFiltration
import Langlands.VirtualRepresentation.ExactTensor
import Langlands.Weil.Representation.CharacterLine

/-! # Exact classes of upper triangular continuous representations -/

noncomputable section

universe uG uV uW

namespace Langlands.FiniteRepresentation

open VirtualRepresentation

variable {G : Type uG} [Group G]

section LineQuotient

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (T : Subrepresentation ρ) (P : Submodule ℂ T.toSubmodule)
  (hP : ∀ g, P ≤ P.comap (T.toRepresentation g)) (w : T.toSubmodule) (χ : G →* ℂˣ)

/-- The linear map `c ↦ [c w]` from the character line to a quotient. -/
def lineQuotientMap : ULift.{uV} ℂ →ₗ[ℂ] T.toSubmodule ⧸ P :=
  P.mkQ ∘ₗ LinearMap.toSpanSingleton ℂ T.toSubmodule w ∘ₗ
    (ULift.moduleEquiv (R := ℂ) (M := ℂ)).toLinearMap

theorem lineQuotientMap_apply (c : ULift.{uV} ℂ) :
    lineQuotientMap T P w c = Submodule.Quotient.mk (c.down • w) := rfl

variable {T P w χ}

/-- A one-dimensional successive quotient spanned by a vector on which `G` acts
by `χ` modulo the lower step is the character line of `χ`. -/
def lineQuotientEquiv
    (hspan : ∀ x : T.toSubmodule, ∃ c : ℂ, x - c • w ∈ P)
    (hind : ∀ c : ℂ, c • w ∈ P → c = 0)
    (hact : ∀ g, T.toRepresentation g w - (χ g : ℂ) • w ∈ P) :
    (characterLine.{uG, uV} χ).representation.Equiv (T.toRepresentation.quotient P hP) :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective (lineQuotientMap T P w)
      ⟨by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro c hc
        rw [lineQuotientMap_apply, Submodule.Quotient.mk_eq_zero] at hc
        exact ULift.ext _ _ (hind _ hc),
      by
        intro q
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P q
        obtain ⟨c, hc⟩ := hspan x
        exact ⟨ULift.up c, (Submodule.Quotient.eq P).mpr (by
          rw [← neg_mem_iff, neg_sub]; exact hc)⟩⟩)
    (fun g => LinearMap.ext fun (c : ULift.{uV} ℂ) => by
      change lineQuotientMap T P w (ULift.up ((χ g : ℂ) * c.down)) =
        (T.toRepresentation.quotient P hP g) (lineQuotientMap T P w c)
      rw [lineQuotientMap_apply, lineQuotientMap_apply, Representation.quotient_apply,
        Submodule.mapQ_apply, map_smul]
      apply (Submodule.Quotient.eq P).mpr
      have h := P.smul_mem c.down (hact g)
      rw [← neg_mem_iff]
      convert h using 1
      simp only [smul_sub, mul_smul, neg_sub]
      rw [smul_comm c.down (χ g : ℂ) w])

end LineQuotient

section Flag

variable (A : FiniteRepresentation.{0, uG, uV} ℂ G) {n : ℕ} (b : Module.Basis (Fin n) ℂ A)

/-- Every group element moves `b j` into the span of `b 0, …, b j`: the coordinate
of `g (b j)` along `b i` vanishes for `j < i`. -/
def IsUpperTriangularBasis : Prop :=
  ∀ (g : G) (i j : Fin n), j < i → b.repr (A.representation g (b j)) i = 0

/-- The span of the first `k` basis vectors. -/
def flagSubmodule (k : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ (b '' {l | l.val < k})

theorem mem_flagSubmodule_iff (k : ℕ) (v : A) :
    v ∈ flagSubmodule A b k ↔ ∀ l : Fin n, k ≤ l.val → b.repr v l = 0 := by
  rw [flagSubmodule, b.mem_span_image]
  constructor
  · intro h l hl
    by_contra hne
    have hmem : l ∈ ((b.repr v).support : Set (Fin n)) :=
      Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne)
    have := h hmem
    simp only [Set.mem_ofPred_eq] at this
    omega
  · intro h l hl
    simp only [Set.mem_ofPred_eq]
    by_contra hk
    exact (Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hl)) (h l (by omega))

variable {A b}

theorem flagSubmodule_le_comap (hb : IsUpperTriangularBasis A b) (k : ℕ) (g : G) :
    flagSubmodule A b k ≤ (flagSubmodule A b k).comap (A.representation g) := by
  rw [flagSubmodule, Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  rw [← flagSubmodule, mem_flagSubmodule_iff]
  intro l hl
  simp only [Set.mem_ofPred_eq] at hj
  exact hb g l j (Fin.lt_def.mpr (by omega))

/-- The invariant span of the first `k` basis vectors. -/
def flagSubrepresentation (hb : IsUpperTriangularBasis A b) (k : ℕ) :
    Subrepresentation A.representation where
  toSubmodule := flagSubmodule A b k
  apply_mem_toSubmodule g _ hv := flagSubmodule_le_comap hb k g hv

theorem flagSubmodule_mono {k k' : ℕ} (h : k ≤ k') :
    flagSubmodule A b k ≤ flagSubmodule A b k' :=
  Submodule.span_mono (Set.image_mono fun l (hl : l.val < k) => lt_of_lt_of_le hl h)

theorem flagSubmodule_zero : flagSubmodule A b 0 = ⊥ := by
  simp [flagSubmodule]

theorem flagSubmodule_length : flagSubmodule A b n = ⊤ := by
  have h : {l : Fin n | l.val < n} = Set.univ := Set.eq_univ_of_forall fun l => l.isLt
  rw [flagSubmodule, h, Set.image_univ, b.span_eq]

/-- The flag of an upper triangular basis as an actual object filtration. -/
def flagFiltration (hb : IsUpperTriangularBasis A b) : ObjectRepFiltration A.obj n :=
  ObjectRepFiltration.ofSubrepresentations (fun k => flagSubrepresentation hb k.val)
    (fun _ _ h _ hv => flagSubmodule_mono (Fin.le_def.mp h) hv)
    (Subrepresentation.ext flagSubmodule_zero)
    (Subrepresentation.ext flagSubmodule_length)

end Flag

section Transfer

variable {A : FiniteRepresentation.{0, uG, uV} ℂ G} {B : FiniteRepresentation.{0, uG, uW} ℂ G}

/-- Coordinates of the action in a basis moved along a representation equivalence
are the coordinates of the original action. -/
theorem repr_map_apply (f : Equiv B A) {n : ℕ} (b : Module.Basis (Fin n) ℂ B) (g : G)
    (i j : Fin n) :
    (b.map f.toLinearEquiv).repr (A.representation g (b.map f.toLinearEquiv j)) i =
      b.repr (B.representation g (b j)) i := by
  have h : A.representation g (f.toLinearEquiv (b j)) =
      f.toLinearEquiv (B.representation g (b j)) :=
    (LinearMap.congr_fun (f.isIntertwining' g) (b j)).symm
  rw [Module.Basis.map_apply, h, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

theorem IsUpperTriangularBasis.map (f : Equiv B A) {n : ℕ} {b : Module.Basis (Fin n) ℂ B}
    (hb : IsUpperTriangularBasis B b) : IsUpperTriangularBasis A (b.map f.toLinearEquiv) :=
  fun g i j hij => (repr_map_apply f b g i j).trans (hb g i j hij)

end Transfer

section Class

variable [TopologicalSpace G]

/-- The exact class of a continuous representation with an upper triangular basis
is the sum of the classes of its diagonal characters. -/
theorem ofRepresentation_eq_sum_characterClass_of_triangular
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hA : A.IsContinuous) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ A) (χ : Fin n → G →ₜ* ℂˣ)
    (hb : IsUpperTriangularBasis A b)
    (hdiag : ∀ (g : G) (i : Fin n), b.repr (A.representation g (b i)) i = χ i g) :
    ExactGrothendieckGroup.ofRepresentation
        (fun B : FiniteRepresentation.{0, uG, uV} ℂ G => B.IsContinuous) ⟨A, hA⟩ =
      ∑ i, ExactGrothendieckGroup.characterClass.{uG, uV} (χ i) := by
  rw [VirtualRepresentation.Weil.exactClass_eq_sum_of_filtration ⟨A, hA⟩ (flagFiltration hb)]
  refine Finset.sum_congr rfl fun i _ => ?_
  let T := flagSubrepresentation hb i.succ.val
  let P : Submodule ℂ T.toSubmodule :=
    (flagSubmodule A b i.castSucc.val).comap T.toSubmodule.subtype
  have hbi : b i ∈ T.toSubmodule := Submodule.subset_span ⟨i, by simp, rfl⟩
  let w : T.toSubmodule := ⟨b i, hbi⟩
  have hmemP : ∀ x : T.toSubmodule, x ∈ P ↔ ∀ l : Fin n, i.val ≤ l.val → b.repr x l = 0 :=
    fun x => mem_flagSubmodule_iff A b _ _
  have hhigh : ∀ x : T.toSubmodule, ∀ l : Fin n, i.val < l.val → b.repr x l = 0 :=
    fun x l hl => (mem_flagSubmodule_iff A b _ _).mp x.property l (by simp; omega)
  have hspan : ∀ x : T.toSubmodule, ∃ c : ℂ, x - c • w ∈ P := by
    intro x
    refine ⟨b.repr x i, (hmemP _).mpr fun l hl => ?_⟩
    rcases Nat.lt_or_eq_of_le hl with hlt | heq
    · simp only [Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul,
        Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hhigh x l hlt, b.repr_self, Finsupp.single_apply,
        ite_eq_right (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)]
      simp
    · have hli : l = i := Fin.ext heq.symm
      subst hli
      simp [w]
  have hind : ∀ c : ℂ, c • w ∈ P → c = 0 := by
    intro c hc
    have := (hmemP _).mp hc i le_rfl
    simpa [w] using this
  have hact : ∀ g, T.toRepresentation g w - ((χ i).toMonoidHom g : ℂ) • w ∈ P := by
    intro g
    refine (hmemP _).mpr fun l hl => ?_
    change b.repr (A.representation g (b i) - ((χ i) g : ℂ) • b i) l = 0
    rcases Nat.lt_or_eq_of_le hl with hlt | heq
    · rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
        hb g l i (Fin.lt_def.mpr hlt), b.repr_self, Finsupp.single_apply,
        ite_eq_right (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)]
      simp
    · have hli : l = i := Fin.ext heq.symm
      subst hli
      rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, hdiag, b.repr_self,
        Finsupp.single_eq_same]
      simp
  have hP : ∀ g, P ≤ P.comap (T.toRepresentation g) := fun g x hx =>
    flagSubmodule_le_comap hb _ g hx
  let e := lineQuotientEquiv (T := T) (P := P) hP (χ := (χ i).toMonoidHom) hspan hind hact
  exact (ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _ e).symm

/-- The same conclusion for any representation equivalent to one with an upper
triangular basis. -/
theorem ofRepresentation_eq_sum_characterClass_of_equiv_triangular
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hA : A.IsContinuous)
    (B : FiniteRepresentation.{0, uG, uW} ℂ G) (f : Equiv B A) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ B) (χ : Fin n → G →ₜ* ℂˣ)
    (hb : IsUpperTriangularBasis B b)
    (hdiag : ∀ (g : G) (i : Fin n), b.repr (B.representation g (b i)) i = χ i g) :
    ExactGrothendieckGroup.ofRepresentation
        (fun C : FiniteRepresentation.{0, uG, uV} ℂ G => C.IsContinuous) ⟨A, hA⟩ =
      ∑ i, ExactGrothendieckGroup.characterClass.{uG, uV} (χ i) :=
  ofRepresentation_eq_sum_characterClass_of_triangular A hA (b.map f.toLinearEquiv) χ
    (hb.map f) fun g i => (repr_map_apply f b g i i).trans (hdiag g i)

/-- If the exact classes of `A` and `A'` are sums of character classes `χ_i` and
`η_j`, the exact class of `A ⊗ A'` is the double sum of the classes of `χ_i η_j`. -/
theorem ofRepresentation_tensor_eq_sum_characterClass
    (A A' : FiniteRepresentation.{0, uG, uV} ℂ G) (hA : A.IsContinuous)
    (hA' : A'.IsContinuous) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι → G →ₜ* ℂˣ) (η : κ → G →ₜ* ℂˣ)
    (h : ExactGrothendieckGroup.ofRepresentation
        (fun C : FiniteRepresentation.{0, uG, uV} ℂ G => C.IsContinuous) ⟨A, hA⟩ =
      ∑ i, ExactGrothendieckGroup.characterClass.{uG, uV} (χ i))
    (h' : ExactGrothendieckGroup.ofRepresentation
        (fun C : FiniteRepresentation.{0, uG, uV} ℂ G => C.IsContinuous) ⟨A', hA'⟩ =
      ∑ j, ExactGrothendieckGroup.characterClass.{uG, uV} (η j)) :
    ExactGrothendieckGroup.ofRepresentation
        (fun C : FiniteRepresentation.{0, uG, uV} ℂ G => C.IsContinuous)
        ⟨tensor A A', isContinuous_tensor hA hA'⟩ =
      ∑ i, ∑ j, ExactGrothendieckGroup.characterClass.{uG, uV} (χ i * η j) := by
  rw [← ExactGrothendieckGroup.continuousTensor_ofRepresentation ⟨A, hA⟩ ⟨A', hA'⟩, h, h',
    LinearMap.map_sum₂]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (ExactGrothendieckGroup.continuousTensor_characterClass (η j) _).trans ?_
  rw [ExactGrothendieckGroup.continuousTwist_characterClass]
  congr 1
  exact ContinuousMonoidHom.ext fun g => mul_comm _ _

end Class

end Langlands.FiniteRepresentation
