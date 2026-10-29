import Langlands.Representation.Filtration.LengthTwoMatching
import Langlands.Representation.Category.Subquotients

/-! Detecting length two through a functor whose induced map on subrepresentation
lattices is strictly monotone. -/

namespace Langlands

namespace FunctorLengthTwo

universe uG uG' uV uV' uW

open CategoryTheory Representation
open LengthCriterionProof (quotientRep lower)

section Rep

variable {k : Type*} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- The inclusion of an invariant subspace as an intertwining map. -/
def subtypeMap (K : Subrepresentation ρ) : K.toRepresentation.IntertwiningMap ρ where
  toLinearMap := K.toSubmodule.subtype
  isIntertwining' _ := rfl

theorem subtypeMap_apply (K : Subrepresentation ρ) (v : K.toSubmodule) :
    subtypeMap K v = (v : V) := rfl

/-- The successive quotient of the whole representation by zero is the representation. -/
theorem nonempty_quotientBotTop_equiv (σ : Representation k G W) :
    Nonempty ((quotientRep (⊥ : Subrepresentation σ) ⊤).Equiv σ) := by
  let p := lower (⊥ : Subrepresentation σ) ⊤
  have hp : p ≤ LinearMap.ker (⊤ : Subrepresentation σ).toSubmodule.subtype := by
    intro x hx
    rw [LinearMap.mem_ker]
    exact (Submodule.mem_bot k).1 hx
  let L := p.liftQ (⊤ : Subrepresentation σ).toSubmodule.subtype hp
  have hL (x : (⊤ : Subrepresentation σ).toSubmodule) :
      L (Submodule.Quotient.mk x) = (x : W) := rfl
  let Ψ : (quotientRep (⊥ : Subrepresentation σ) ⊤).IntertwiningMap σ :=
    { toLinearMap := L
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro q
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rfl }
  refine ⟨Ψ.ofBijective ⟨?_, ?_⟩⟩
  · intro q q' hqq'
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
    change L (Submodule.Quotient.mk x) = L (Submodule.Quotient.mk y) at hqq'
    rw [hL, hL] at hqq'
    rw [Subtype.ext hqq']
  · intro w
    exact ⟨Submodule.Quotient.mk ⟨w, Submodule.mem_top⟩, rfl⟩

/-- The successive quotient of an invariant subspace by zero is the subspace. -/
theorem nonempty_quotientBot_equiv (K : Subrepresentation ρ) :
    Nonempty ((quotientRep (⊥ : Subrepresentation ρ) K).Equiv K.toRepresentation) := by
  obtain ⟨e₁⟩ := LengthTwo.nonempty_gradedEquiv (subtypeMap K)
    (S := (⊥ : Subrepresentation K.toRepresentation)) (T := ⊤) (S' := ⊥) (T' := K)
    (fun v _ => v.2) (fun w hw => ⟨⟨w, hw⟩, Submodule.mem_top, rfl⟩)
    (fun v _ => by
      exact (Submodule.mem_bot k).trans
        (ZeroMemClass.coe_eq_zero.trans (Submodule.mem_bot k).symm))
  obtain ⟨e₀⟩ := nonempty_quotientBotTop_equiv K.toRepresentation
  exact ⟨e₁.symm.trans e₀⟩

/-- An injective intertwining map identifies its source with its range. -/
theorem nonempty_equiv_range (g : ρ.IntertwiningMap σ) (hg : Function.Injective g) :
    Nonempty (ρ.Equiv g.range.toRepresentation) := by
  obtain ⟨e₀⟩ := nonempty_quotientBotTop_equiv ρ
  obtain ⟨e₁⟩ := LengthTwo.nonempty_gradedEquiv g
    (S := (⊥ : Subrepresentation ρ)) (T := ⊤) (S' := ⊥) (T' := g.range)
    (fun v _ => (IntertwiningMap.mem_range _ _ g _).2 ⟨v, rfl⟩)
    (fun w hw => by
      obtain ⟨v, hv⟩ := (IntertwiningMap.mem_range _ _ g w).1 hw
      exact ⟨v, Submodule.mem_top, hv⟩)
    (fun v _ => by
      exact (Submodule.mem_bot k).trans ((map_eq_zero_iff g hg).trans (Submodule.mem_bot k).symm))
  obtain ⟨e₂⟩ := nonempty_quotientBot_equiv g.range
  exact ⟨e₀.symm.trans (e₁.trans e₂)⟩

/-- An irreducible invariant subspace is nonzero. -/
theorem ne_bot_of_isIrreducible {K : Subrepresentation ρ}
    (hK : IsIrreducible K.toRepresentation) : K ≠ ⊥ := by
  intro h
  apply IsSimpleOrder.bot_ne_top (α := Subrepresentation K.toRepresentation)
  refine le_antisymm bot_le fun v _ => ?_
  rw [LengthTwo.mem_bot_iff]
  have hv : (v : V) ∈ (⊥ : Subrepresentation ρ) := h ▸ v.2
  exact Subtype.ext ((LengthTwo.mem_bot_iff _).1 hv)

/-- An invariant subspace of an irreducible invariant subspace is zero or all of it. -/
theorem eq_bot_or_eq_of_le_of_isIrreducible {K L : Subrepresentation ρ}
    (hK : IsIrreducible K.toRepresentation) (hLK : L ≤ K) : L = ⊥ ∨ L = K := by
  rcases hK.eq_bot_or_eq_top (LengthTwo.comap (subtypeMap K) L) with h | h
  · left
    refine le_antisymm (fun v hv => ?_) bot_le
    have hmem : (⟨v, hLK hv⟩ : K.toSubmodule) ∈ LengthTwo.comap (subtypeMap K) L := hv
    rw [h, LengthTwo.mem_bot_iff] at hmem
    rw [LengthTwo.mem_bot_iff]
    exact congrArg Subtype.val hmem
  · right
    refine le_antisymm hLK fun v hv => ?_
    have hmem : (⟨v, hv⟩ : K.toSubmodule) ∈ LengthTwo.comap (subtypeMap K) L := by
      rw [h]
      exact LengthTwo.mem_top _
    exact hmem

/-- The modular-lattice covering transfer for invariant subspaces. -/
theorem inf_covBy_of_covBy_sup {a b : Subrepresentation ρ} (h : a ⋖ a ⊔ b) : a ⊓ b ⋖ b := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have h' : e a ⋖ e a ⊔ e b := by
    rw [← e.map_sup]
    exact (apply_covBy_apply_iff e).2 h
  have h'' := inf_covBy_of_covBy_sup_left h'
  rw [← e.map_inf] at h''
  exact (apply_covBy_apply_iff e).1 h''

/-- A length-two filtration with simple factors whose lower step is the only
irreducible invariant subspace leaves no other invariant subspace. -/
theorem eq_bot_or_eq_or_eq_top (s : ObjectRepFiltration (Rep.of ρ) 2)
    (hs : s.HasSimpleFactors)
    (huniq : ∀ K : Subrepresentation ρ, IsIrreducible K.toRepresentation →
      K = s.subrepresentation 1)
    (M : Subrepresentation ρ) :
    M = ⊥ ∨ M = s.subrepresentation 1 ∨ M = ⊤ := by
  have hcov := (LengthCriterionProof.hasSimpleFactors_iff_covBy s).1 hs
  have h₀ : (⊥ : Subrepresentation ρ) ⋖ s.subrepresentation 1 := by
    have := hcov 0
    rw [show (0 : Fin 2).castSucc = 0 from rfl, ObjectRepFiltration.subrepresentation_zero]
      at this
    exact this
  have h₁ : s.subrepresentation 1 ⋖ ⊤ := by
    have := hcov 1
    rw [show (1 : Fin 2).succ = Fin.last 2 from rfl,
      ObjectRepFiltration.subrepresentation_last] at this
    exact this
  set S := s.subrepresentation 1
  rcases h₀.eq_or_eq (bot_le : ⊥ ≤ M ⊓ S) inf_le_right with h | h
  · by_cases hM : M = ⊥
    · exact Or.inl hM
    exfalso
    have hMS : ¬ M ≤ S := fun hle => hM (by rwa [inf_eq_left.2 hle] at h)
    have hsup : S ⊔ M = ⊤ :=
      (h₁.eq_or_eq le_sup_left le_top).resolve_left fun he => hMS (he ▸ le_sup_right)
    have hcovM : S ⊓ M ⋖ M := inf_covBy_of_covBy_sup (by rw [hsup]; exact h₁)
    rw [inf_comm, h] at hcovM
    have hirr : IsIrreducible M.toRepresentation := by
      obtain ⟨e⟩ := nonempty_quotientBot_equiv M
      exact LengthTwo.isIrreducible_of_equiv e
        ((LengthCriterionProof.isIrreducible_quotientRep_iff bot_le).2 hcovM)
    have hMeq := huniq M hirr
    rw [hMeq, inf_idem] at h
    exact h₀.lt.ne' h
  · have hSM : S ≤ M := h ▸ inf_le_left
    rcases h₁.eq_or_eq hSM le_top with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

theorem comap_bot_of_injective (g : ρ.IntertwiningMap σ) (hg : Function.Injective g) :
    LengthTwo.comap g ⊥ = ⊥ := by
  refine le_antisymm (fun v hv => ?_) bot_le
  have hv' : g v ∈ (⊥ : Subrepresentation σ) := hv
  rw [LengthTwo.mem_bot_iff] at hv' ⊢
  exact (map_eq_zero_iff g hg).1 hv'

theorem comap_top (g : ρ.IntertwiningMap σ) : LengthTwo.comap g ⊤ = ⊤ :=
  le_antisymm le_top fun _ _ => LengthTwo.mem_top _

theorem comap_comap_symm (φ : ρ.Equiv σ) (M : Subrepresentation ρ) :
    LengthTwo.comap φ.toIntertwiningMap (LengthTwo.comap φ.symm.toIntertwiningMap M) = M := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change φ.symm (φ v) ∈ M ↔ v ∈ M
  rw [LengthTwo.equiv_symm_apply_apply]

/-- Transport of the length-two lattice data along an equivalence `ρ ≃ σ`. -/
theorem exists_middle_of_equiv {U : Type*} [AddCommGroup U] [Module k U]
    {X : Type*} [AddCommGroup X] [Module k X]
    {τ : Representation k G U} {υ : Representation k G X}
    (φ : ρ.Equiv σ) (s : ObjectRepFiltration (Rep.of σ) 2) (hs : s.HasSimpleFactors)
    (huniq : ∀ K : Subrepresentation σ, IsIrreducible K.toRepresentation →
      K = s.subrepresentation 1)
    (θ : τ.Equiv υ)
    (hne : ¬ Nonempty ((s.gradedRepresentation 0).ρ.Equiv υ)) :
    ∃ S : Subrepresentation ρ, S ≠ ⊥ ∧ S ≠ ⊤ ∧
      (∀ M : Subrepresentation ρ, M = ⊥ ∨ M = S ∨ M = ⊤) ∧
      ¬ Nonempty (S.toRepresentation.Equiv τ) := by
  have hcov := (LengthCriterionProof.hasSimpleFactors_iff_covBy s).1 hs
  have h₀ : (⊥ : Subrepresentation σ) ⋖ s.subrepresentation 1 := by
    have := hcov 0
    rw [show (0 : Fin 2).castSucc = 0 from rfl, ObjectRepFiltration.subrepresentation_zero]
      at this
    exact this
  have h₁ : s.subrepresentation 1 ⋖ ⊤ := by
    have := hcov 1
    rw [show (1 : Fin 2).succ = Fin.last 2 from rfl,
      ObjectRepFiltration.subrepresentation_last] at this
    exact this
  have hφ : Function.Injective φ.toIntertwiningMap := φ.injective
  have hφs : Function.Injective φ.symm.toIntertwiningMap := φ.symm.injective
  refine ⟨LengthTwo.comap φ.toIntertwiningMap (s.subrepresentation 1), ?_, ?_, ?_, ?_⟩
  · intro h
    apply h₀.lt.ne'
    rw [← comap_comap_symm φ.symm (s.subrepresentation 1)]
    change LengthTwo.comap φ.symm.toIntertwiningMap
      (LengthTwo.comap φ.toIntertwiningMap (s.subrepresentation 1)) = ⊥
    rw [h, comap_bot_of_injective _ hφs]
  · intro h
    apply h₁.lt.ne
    rw [← comap_comap_symm φ.symm (s.subrepresentation 1)]
    change LengthTwo.comap φ.symm.toIntertwiningMap
      (LengthTwo.comap φ.toIntertwiningMap (s.subrepresentation 1)) = ⊤
    rw [h, comap_top]
  · intro M
    rw [← comap_comap_symm φ M]
    rcases eq_bot_or_eq_or_eq_top s hs huniq
      (LengthTwo.comap φ.symm.toIntertwiningMap M) with h | h | h
    · left
      rw [h, comap_bot_of_injective _ hφ]
    · right; left
      rw [h]
    · right; right
      rw [h, comap_top]
  · rintro ⟨e⟩
    apply hne
    obtain ⟨e₁⟩ := LengthTwo.nonempty_gradedEquiv φ.symm.toIntertwiningMap
      (S := (⊥ : Subrepresentation σ)) (T := s.subrepresentation 1) (S' := ⊥)
      (T' := LengthTwo.comap φ.toIntertwiningMap (s.subrepresentation 1))
      (fun w hw => by
        change φ (φ.symm w) ∈ s.subrepresentation 1
        rw [LengthTwo.equiv_apply_symm_apply]
        exact hw)
      (fun v hv => ⟨φ v, hv, LengthTwo.equiv_symm_apply_apply φ v⟩)
      (fun w _ => by
        exact (Submodule.mem_bot k).trans
          ((map_eq_zero_iff _ hφs).trans (Submodule.mem_bot k).symm))
    obtain ⟨e₂⟩ := nonempty_quotientBot_equiv
      (LengthTwo.comap φ.toIntertwiningMap (s.subrepresentation 1))
    change Nonempty ((quotientRep (s.subrepresentation (0 : Fin 2).castSucc)
      (s.subrepresentation (0 : Fin 2).succ)).Equiv υ)
    rw [show (0 : Fin 2).castSucc = 0 from rfl, ObjectRepFiltration.subrepresentation_zero]
    exact ⟨e₁.trans (e₂.trans (e.trans θ))⟩

end Rep

section ThreeCount

variable {α : Type*} [PartialOrder α] [BoundedOrder α]

open Classical in
/-- The count `0, 1, 2` of `⊥`, a strictly intermediate element and `⊤`. -/
noncomputable def threeCount (M : α) : ℕ :=
  if M = ⊥ then 0 else if M = ⊤ then 2 else 1

theorem threeCount_le_two (M : α) : threeCount M ≤ 2 := by
  unfold threeCount
  split_ifs <;> omega

theorem threeCount_eq_one_iff (M : α) : threeCount M = 1 ↔ M ≠ ⊥ ∧ M ≠ ⊤ := by
  unfold threeCount
  split_ifs <;> simp_all

/-- On a bounded order whose only elements are `⊥`, `S` and `⊤`, the count is
strictly monotone. -/
theorem threeCount_strictMono {S : α} (h0 : S ≠ ⊥) (h2 : S ≠ ⊤)
    (hS : ∀ M : α, M = ⊥ ∨ M = S ∨ M = ⊤) : StrictMono (threeCount (α := α)) := by
  have htb : (⊤ : α) ≠ ⊥ := fun h => h0 (eq_bot_iff.2 (h ▸ le_top))
  intro a b hab
  rcases hS a with rfl | rfl | rfl
  · have hb : b ≠ ⊥ := ne_bot_of_gt hab
    unfold threeCount
    split_ifs <;> simp_all
  · rcases hS b with rfl | rfl | rfl
    · exact absurd hab not_lt_bot
    · exact absurd hab (lt_irrefl _)
    · unfold threeCount
      simp [h0, h2, htb]
  · exact absurd hab not_top_lt

end ThreeCount

section Smooth

universe uR

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  {G' : Type uG'} [Group G'] [TopologicalSpace G']
  (D : SmoothRep.{uR, uG, uV} k G ⥤ SmoothRep.{uR, uG', uV'} k G')

/-- Length two through a functor. Let `f : X → Y` be a nonzero intertwining map
onto an irreducible `Y`. Suppose `D` strictly preserves inclusions of invariant
subspaces of `X`, measured by the images of the inclusions, that the invariant
subspaces of `D X` are exactly `⊥`, `S` and `⊤` with `S` strictly intermediate,
that `D Y` is irreducible and that `S` is not equivalent to `D Y`. Then `0 ⊆ ker f
⊆ X` is a composition series whose top factor is `Y`, whose bottom factor is not
equivalent to `Y`, and whose bottom step is the only irreducible invariant
subspace of `X`. -/
theorem lengthTwo_of_strictMono (X Y : SmoothRep.{uR, uG, uV} k G)
    (f : X.representation.IntertwiningMap Y.representation) (hf : f ≠ 0)
    (hY : Y.IsIrreducible)
    (hmono : ∀ K₁ K₂ : Subrepresentation X.representation, K₁ < K₂ →
      (SmoothRep.hom (D.map (SmoothRep.subtype X K₁))).range <
        (SmoothRep.hom (D.map (SmoothRep.subtype X K₂))).range)
    (S : Subrepresentation (D.obj X).representation) (hS0 : S ≠ ⊥) (hS2 : S ≠ ⊤)
    (hS : ∀ M : Subrepresentation (D.obj X).representation, M = ⊥ ∨ M = S ∨ M = ⊤)
    (hDY : (D.obj Y).IsIrreducible)
    (hne : ¬ Nonempty (S.toRepresentation.Equiv (D.obj Y).representation)) :
    ∃ s : ObjectRepFiltration (Rep.of X.representation) 2,
      s.HasSimpleFactors ∧
        Nonempty ((s.gradedRepresentation 1).ρ.Equiv Y.representation) ∧
        ¬ Nonempty ((s.gradedRepresentation 0).ρ.Equiv Y.representation) ∧
        ∀ K : Subrepresentation X.representation,
          IsIrreducible K.toRepresentation → K = s.subrepresentation 1 := by
  classical
  let Φ : Subrepresentation X.representation → Subrepresentation (D.obj X).representation :=
    fun K => (SmoothRep.hom (D.map (SmoothRep.subtype X K))).range
  have hΦ : StrictMono Φ := fun a b h => hmono a b h
  let μ : Subrepresentation X.representation → ℕ := fun K => threeCount (Φ K)
  have hμ : StrictMono μ := (threeCount_strictMono hS0 hS2 hS).comp hΦ
  have hμ2 : ∀ K, μ K ≤ 2 := fun K => threeCount_le_two _
  -- A strictly intermediate invariant subspace has image `S`.
  have hmid : ∀ K, K ≠ ⊥ → K ≠ ⊤ → Φ K = S := by
    intro K h0 h2
    have h1 := hμ (bot_lt_iff_ne_bot.2 h0)
    have h3 := hμ (lt_top_iff_ne_top.2 h2)
    have h4 := hμ2 ⊤
    have hK1 : μ K = 1 := by omega
    obtain ⟨hb, ht⟩ := (threeCount_eq_one_iff _).1 hK1
    rcases hS (Φ K) with h | h | h
    · exact absurd h hb
    · exact h
    · exact absurd h ht
  -- No strictly intermediate invariant subspace is equivalent to `Y`.
  have key : ∀ K : Subrepresentation X.representation, K ≠ ⊥ → K ≠ ⊤ →
      ¬ Nonempty (K.toRepresentation.Equiv Y.representation) := by
    rintro K h0 h2 ⟨e⟩
    let ι := D.map (SmoothRep.subtype X K)
    let isoY : D.obj (SmoothRep.subrepresentation X K) ≅ D.obj Y :=
      D.mapIso (SmoothRep.mkIso e)
    have hirr : (D.obj (SmoothRep.subrepresentation X K)).IsIrreducible :=
      LengthTwo.isIrreducible_of_equiv (SmoothRep.equivOfIso isoY.symm) hDY
    have hrange : (SmoothRep.hom ι).range = S := hmid K h0 h2
    have := hirr
    rcases Representation.IsIrreducible.injective_or_eq_zero (SmoothRep.hom ι) with hinj | hzero
    · obtain ⟨e'⟩ := nonempty_equiv_range (SmoothRep.hom ι) hinj
      apply hne
      rw [← hrange]
      exact ⟨e'.symm.trans (SmoothRep.equivOfIso isoY)⟩
    · apply hS0
      rw [← hrange]
      refine le_antisymm (fun v hv => ?_) bot_le
      obtain ⟨x, rfl⟩ := (IntertwiningMap.mem_range _ _ _ v).1 hv
      rw [LengthTwo.mem_bot_iff, hzero]
      rfl
  set K₀ := f.ker with hK₀
  have hK₀top : K₀ ≠ ⊤ := LengthTwo.ker_ne_top_of_ne_zero f hf
  have hfrange : f.range = ⊤ :=
    (hY.eq_bot_or_eq_top f.range).resolve_left (LengthTwo.range_ne_bot_of_ne_zero f hf)
  have hfsurj : Function.Surjective f := fun w =>
    (IntertwiningMap.mem_range _ _ f w).1 (hfrange ▸ LengthTwo.mem_top w)
  have hK₀bot : K₀ ≠ ⊥ := by
    intro h
    have hinj : Function.Injective f := by
      intro a b hab
      have hmem : a - b ∈ K₀ :=
        (IntertwiningMap.mem_ker _ _ f _).2 (by rw [map_sub, hab, sub_self])
      rw [h, LengthTwo.mem_bot_iff] at hmem
      exact sub_eq_zero.1 hmem
    have hirr : (D.obj X).IsIrreducible :=
      LengthTwo.isIrreducible_of_equiv
        (SmoothRep.equivOfIso (D.mapIso (SmoothRep.mkIso (f.ofBijective ⟨hinj, hfsurj⟩))).symm)
        hDY
    rcases hirr.eq_bot_or_eq_top S with h' | h'
    · exact hS0 h'
    · exact hS2 h'
  have h1 := hμ (bot_lt_iff_ne_bot.2 hK₀bot)
  have h3 := hμ (lt_top_iff_ne_top.2 hK₀top)
  have h4 := hμ2 ⊤
  have hc₁ : ⊥ ⋖ K₀ :=
    LengthTwo.covBy_of_count hμ (bot_lt_iff_ne_bot.2 hK₀bot) (by omega)
  have hc₂ : K₀ ⋖ ⊤ :=
    LengthTwo.covBy_of_count hμ (lt_top_iff_ne_top.2 hK₀top) (by omega)
  refine ⟨LengthTwo.twoStep K₀, LengthTwo.twoStep_hasSimpleFactors hc₁ hc₂, ?_, ?_, ?_⟩
  · change Nonempty ((quotientRep K₀ ⊤).Equiv Y.representation)
    obtain ⟨e₁⟩ := LengthTwo.nonempty_gradedEquiv f
      (S := K₀) (T := ⊤) (S' := ⊥) (T' := ⊤)
      (fun _ _ => Submodule.mem_top)
      (fun w _ => by
        obtain ⟨v, hv⟩ := hfsurj w
        exact ⟨v, Submodule.mem_top, hv⟩)
      (fun v _ => (Submodule.mem_bot k).trans (IntertwiningMap.mem_ker _ _ f v).symm)
    obtain ⟨e₀⟩ := nonempty_quotientBotTop_equiv Y.representation
    exact ⟨e₁.trans e₀⟩
  · change ¬ Nonempty ((quotientRep ⊥ K₀).Equiv Y.representation)
    rintro ⟨e⟩
    obtain ⟨e₀⟩ := nonempty_quotientBot_equiv K₀
    exact key K₀ hK₀bot hK₀top ⟨e₀.symm.trans e⟩
  · intro K hK
    change K = K₀
    have hKbot := ne_bot_of_isIrreducible hK
    by_cases hle : K ≤ K₀
    · exact (hc₁.eq_or_eq bot_le hle).resolve_left hKbot
    · exfalso
      have hinf : K ⊓ K₀ = ⊥ := by
        rcases eq_bot_or_eq_of_le_of_isIrreducible hK (inf_le_left : K ⊓ K₀ ≤ K) with h | h
        · exact h
        · exact (hle (h ▸ inf_le_right)).elim
      have hKtop : K ≠ ⊤ := by
        rintro rfl
        rw [top_inf_eq] at hinf
        exact hK₀bot hinf
      let g := f.comp (subtypeMap K)
      have hginj : Function.Injective g := by
        intro a b hab
        have hmem : (a : X) - b ∈ K ⊓ K₀ :=
          ⟨sub_mem a.2 b.2, (IntertwiningMap.mem_ker _ _ f _).2 (by
            rw [map_sub]
            exact sub_eq_zero.2 hab)⟩
        rw [hinf, LengthTwo.mem_bot_iff] at hmem
        exact Subtype.ext (sub_eq_zero.1 hmem)
      have : IsIrreducible K.toRepresentation := hK
      have : IsIrreducible Y.representation := hY
      rcases Representation.IsIrreducible.bijective_or_eq_zero g with hbij | hzero
      · exact key K hKbot hKtop ⟨g.ofBijective hbij⟩
      · apply hKbot
        refine le_antisymm (fun v hv => ?_) bot_le
        have hv0 : g ⟨v, hv⟩ = g 0 := by rw [hzero, map_zero]; rfl
        rw [LengthTwo.mem_bot_iff]
        exact congrArg Subtype.val (hginj hv0)

end Smooth

end FunctorLengthTwo

end Langlands
