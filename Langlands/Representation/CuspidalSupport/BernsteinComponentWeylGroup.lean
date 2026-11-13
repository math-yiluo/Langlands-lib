import Langlands.Representation.CuspidalSupport.RationalConjugateInertia
import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # The finite group `W` acting on the unramified twists of a cuspidal datum

For an actual group-scheme embedding `j : H ⟶ G` and a smooth representation `ρ` of `H(F)`,
the self-conjugacies `c` of `j` act on the unramified characters `X(H)` by the affine
permutations `ω ↦ χ * (ω ∘ c)`, for the characters `χ` with `ρ ⊗ χ ≅ ρ^c`. These permutations
form a subgroup `W` of `Perm X(H)`, whose orbits are exactly the classes of the relation
`ρ ⊗ ω ≅ (ρ ⊗ ω')^c`, and which preserves the algebra `ℂ[X(H)]`. Given finitely many
normalizer representatives and a finite twist stabilizer of `ρ`, the group `W` is finite.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.CuspidalSupport.ComponentWeyl

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance instComponentWeylTop (M : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine M.X.left] : TopologicalSpace (GroupScheme.rationalPoints M) :=
  rationalPointTopology F M.X

/-- The unramified characters `X(H)` of the rational points of `H`. -/
abbrev UChar (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left] :=
  unramifiedCharacters (fun χ => (rationalNormCharacters H χ).toMul)

section Isos

variable {H K L : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  [IsAffine K.X.left] [LocallyOfFiniteType K.X.hom]

theorem twist_congr (χ : UChar H) {A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)}
    (h : Nonempty (A ≅ B)) :
    Nonempty (rationalUnramifiedTwist H χ A ≅ rationalUnramifiedTwist H χ B) :=
  h.map (SmoothRep.twistIso _ _)

theorem twist_twist (χ ψ : UChar H) (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) :
    Nonempty (rationalUnramifiedTwist H χ (rationalUnramifiedTwist H ψ A) ≅
      rationalUnramifiedTwist H (χ * ψ) A) :=
  ⟨rationalUnramifiedTwistMulIso H χ ψ A⟩

theorem twist_one (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) :
    Nonempty (rationalUnramifiedTwist H 1 A ≅ A) :=
  ⟨rationalUnramifiedTwistOneIso H A⟩

theorem twist_eq {χ ψ : UChar H} (h : χ = ψ)
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) :
    Nonempty (rationalUnramifiedTwist H χ A ≅ rationalUnramifiedTwist H ψ A) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- Twisting by `χ⁻¹` undoes twisting by `χ`. -/
theorem twist_inv_twist (χ : UChar H) (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) :
    Nonempty (rationalUnramifiedTwist H χ⁻¹ (rationalUnramifiedTwist H χ A) ≅ A) := by
  obtain ⟨e₁⟩ := twist_twist χ⁻¹ χ A
  obtain ⟨e₂⟩ := twist_eq (inv_mul_cancel χ) A
  obtain ⟨e₃⟩ := twist_one A
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩

/-- `A ⊗ χ ≅ B` exactly when `A ≅ B ⊗ χ⁻¹`. -/
theorem twist_iso_iff (χ : UChar H) (A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) :
    Nonempty (rationalUnramifiedTwist H χ A ≅ B) ↔
      Nonempty (A ≅ rationalUnramifiedTwist H χ⁻¹ B) := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨e₁⟩ := twist_inv_twist χ A
    obtain ⟨e₂⟩ := twist_congr χ⁻¹ ⟨e⟩
    exact ⟨e₁.symm ≪≫ e₂⟩
  · rintro ⟨e⟩
    obtain ⟨e₁⟩ := twist_congr χ ⟨e⟩
    obtain ⟨e₂⟩ := twist_inv_twist χ⁻¹ B
    rw [inv_inv] at e₂
    exact ⟨e₁ ≪≫ e₂⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType H.X.hom]
  [LocallyOfFiniteType K.X.hom] in
theorem pullback_congr (e : H ≅ K) {A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints K)}
    (h : Nonempty (A ≅ B)) : Nonempty (rationalIsoPullback e A ≅ rationalIsoPullback e B) :=
  h.map (SmoothRep.pullbackFunctor (rationalPointIso e)).mapIso

theorem pullback_twist (e : H ≅ K) (χ : UChar K)
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints K)) :
    Nonempty (rationalIsoPullback e (rationalUnramifiedTwist K χ A) ≅
      rationalUnramifiedTwist H (rationalUnramifiedCharacterRestrict e.hom χ)
        (rationalIsoPullback e A)) :=
  ⟨rationalIsoPullbackTwistIso e χ A⟩

/-- `A ⊗ χ ≅ B ⊗ ψ` exactly when `A ⊗ (χ ψ⁻¹) ≅ B`. -/
theorem twist_iso_twist_iff (χ ψ : UChar H)
    (A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) :
    Nonempty (rationalUnramifiedTwist H χ A ≅ rationalUnramifiedTwist H ψ B) ↔
      Nonempty (rationalUnramifiedTwist H (χ * ψ⁻¹) A ≅ B) := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨e₁⟩ := twist_eq (mul_comm χ ψ⁻¹) A
    obtain ⟨e₂⟩ := twist_twist ψ⁻¹ χ A
    obtain ⟨e₃⟩ := twist_congr ψ⁻¹ ⟨e⟩
    obtain ⟨e₄⟩ := twist_inv_twist ψ B
    exact ⟨e₁ ≪≫ e₂.symm ≪≫ e₃ ≪≫ e₄⟩
  · rintro ⟨e⟩
    obtain ⟨e₁⟩ := twist_eq (show χ = ψ * (χ * ψ⁻¹) by rw [mul_comm χ ψ⁻¹, mul_inv_cancel_left]) A
    obtain ⟨e₂⟩ := twist_twist ψ (χ * ψ⁻¹) A
    obtain ⟨e₃⟩ := twist_congr ψ ⟨e⟩
    exact ⟨e₁ ≪≫ e₂.symm ≪≫ e₃⟩

end Isos

section Affine

variable {H K : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [IsAffine K.X.left]

theorem restrict_inv_hom (e : H ≅ K) (ω : UChar K) :
    rationalUnramifiedCharacterRestrict e.inv (rationalUnramifiedCharacterRestrict e.hom ω) = ω := by
  rw [← rationalUnramifiedCharacterRestrict_comp, e.inv_hom_id,
    rationalUnramifiedCharacterRestrict_id]

theorem restrict_hom_inv (e : H ≅ K) (ω : UChar H) :
    rationalUnramifiedCharacterRestrict e.hom (rationalUnramifiedCharacterRestrict e.inv ω) = ω := by
  rw [← rationalUnramifiedCharacterRestrict_comp, e.hom_inv_id,
    rationalUnramifiedCharacterRestrict_id]

/-- The affine permutation `ω ↦ χ * (ω ∘ e)` of `X(H)`, for an automorphism `e` of `H`. -/
def affinePerm (e : H ≅ H) (χ : UChar H) : Equiv.Perm (UChar H) where
  toFun ω := χ * rationalUnramifiedCharacterRestrict e.hom ω
  invFun ω := rationalUnramifiedCharacterRestrict e.inv (χ⁻¹ * ω)
  left_inv ω := by
    simp only [inv_mul_cancel_left]
    exact restrict_inv_hom e ω
  right_inv ω := by
    change χ * rationalUnramifiedCharacterRestrict e.hom
      (rationalUnramifiedCharacterRestrict e.inv (χ⁻¹ * ω)) = ω
    rw [restrict_hom_inv, mul_inv_cancel_left]

@[simp]
theorem affinePerm_apply (e : H ≅ H) (χ ω : UChar H) :
    affinePerm e χ ω = χ * rationalUnramifiedCharacterRestrict e.hom ω := rfl

/-- Precomposition with `ω' ↦ χ * (ω' ∘ f)` sends `ℂ[X(H)]` into `ℂ[X(K)]`. -/
theorem comp_affine_mem_regular (f : K ⟶ H) (χ : UChar K) {g : UChar K → ℂ}
    (hg : g ∈ unramifiedRegularFunctions (fun ψ => (rationalNormCharacters K ψ).toMul)) :
    (fun ω => g (χ * rationalUnramifiedCharacterRestrict f ω)) ∈
      unramifiedRegularFunctions (fun ψ => (rationalNormCharacters H ψ).toMul) := by
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    have : (fun ω : UChar H => unramifiedEvaluation
        (fun ψ => (rationalNormCharacters K ψ).toMul) m
          (χ * rationalUnramifiedCharacterRestrict f ω)) =
        (χ.val m : ℂ) • unramifiedEvaluation (fun ψ => (rationalNormCharacters H ψ).toMul)
          (GroupScheme.rationalPoints.map f m) := by
      funext ω
      simp [unramifiedEvaluation]
    rw [this]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self _)) _
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy

end Affine

section Conjugation

variable {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

omit [LocallyOfFiniteType H.X.hom] in
/-- An unramified character is invariant under inner automorphisms. -/
theorem restrict_innerIso (m : GroupScheme.rationalPoints H) (ω : UChar H) :
    rationalUnramifiedCharacterRestrict (H.innerIso m).hom ω = ω := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro x
  rw [rationalUnramifiedCharacterRestrict_apply, GroupScheme.rationalPoints_map_innerIso]
  change ω.val (m * x * m⁻¹) = ω.val x
  rw [map_mul, map_mul, map_inv]
  exact mul_inv_cancel_comm _ _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType H.X.hom] in
/-- Two algebraic isomorphisms differing by an inner automorphism give isomorphic pullbacks. -/
theorem pullback_iso_of_conj {K : GroupScheme (Spec (CommRingCat.of F))} [IsAffine K.X.left]
    (e e' : H ≅ K) (n : GroupScheme.rationalPoints K)
    (h : ∀ x, GroupScheme.rationalPoints.map e.hom x =
      n * GroupScheme.rationalPoints.map e'.hom x * n⁻¹)
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints K)) :
    Nonempty (rationalIsoPullback e' A ≅ rationalIsoPullback e A) := by
  let L : A ≃ₗ[ℂ] A := LinearEquiv.ofLinearMap (A.representation n) (A.representation n⁻¹)
    (by ext y; simp) (by ext y; simp)
  let R : (rationalIsoPullback e' A).representation.Equiv
      (rationalIsoPullback e A).representation :=
    Representation.Equiv.mk L (fun x => by
      have key : ∀ v : A, A.representation n
          (A.representation (GroupScheme.rationalPoints.map e'.hom x) v) =
          A.representation (GroupScheme.rationalPoints.map e.hom x) (A.representation n v) := by
        intro v
        rw [h, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      ext v
      exact key v)
  exact ⟨SmoothRep.mkIso R⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom] in
/-- Two self-conjugacies of a monomorphism whose points differ by a point of the source differ
by the corresponding inner automorphism of the source. -/
theorem iso_hom_eq_of_point_eq {j : H ⟶ G} (hj : Mono j.hom.hom)
    (c c' : RationalLeviConjugacy j j) (m : GroupScheme.rationalPoints H)
    (h : c.point = c'.point * GroupScheme.rationalPoints.map j m) :
    c.iso.hom = (H.innerIso m).hom ≫ c'.iso.hom := by
  have : Mono j := ⟨fun f g hfg => Grp.hom_ext _ _ ((cancel_mono j.hom.hom).1 (by
    have := congrArg (fun φ => φ.hom.hom) hfg
    simpa only [Grp.comp_hom_hom] using this))⟩
  rw [← cancel_mono j, ← c.commutes, Category.assoc, ← c'.commutes, h,
    G.innerIso_mul_hom, ← Category.assoc,
    show j ≫ (G.innerIso (GroupScheme.rationalPoints.map j m)).hom = (H.innerIso m).hom ≫ j from
      (GroupScheme.innerIso_hom_comp j m).symm, Category.assoc]

end Conjugation

section Weyl

variable {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The characters `χ` with `ρ ⊗ χ ≅ ρ^e`. -/
def twistSet (ρ : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) (e : H ≅ H) :
    Set (UChar H) :=
  {χ | Nonempty (rationalUnramifiedTwist H χ ρ ≅ rationalIsoPullback e ρ)}

/-- `ρ ⊗ ω ≅ (ρ ⊗ ω')^e` exactly when `ω (ω' ∘ e)⁻¹` lies in the twist set of `e`. -/
theorem iso_pullback_twist_iff (ρ : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H))
    (e : H ≅ H) (ω ω' : UChar H) :
    Nonempty (rationalUnramifiedTwist H ω ρ ≅
        rationalIsoPullback e (rationalUnramifiedTwist H ω' ρ)) ↔
      ω * (rationalUnramifiedCharacterRestrict e.hom ω')⁻¹ ∈ twistSet ρ e := by
  obtain ⟨p⟩ := pullback_twist e ω' ρ
  rw [twistSet, Set.mem_ofPred_eq, ← twist_iso_twist_iff]
  exact ⟨fun ⟨q⟩ => ⟨q ≪≫ p⟩, fun ⟨q⟩ => ⟨q ≪≫ p.symm⟩⟩

/-- The group `W`: the affine permutations `ω ↦ χ (ω ∘ c)` for the self-conjugacies `c` of `j`
and the characters `χ` with `ρ ⊗ χ ≅ ρ^c`. -/
def weylGroup (j : H ⟶ G) (ρ : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) :
    Subgroup (Equiv.Perm (UChar H)) where
  carrier := {σ | ∃ c : RationalLeviConjugacy j j, ∃ χ ∈ twistSet ρ c.iso,
    σ = affinePerm c.iso χ}
  one_mem' := by
    refine ⟨RationalLeviConjugacy.refl j, 1, ?_, ?_⟩
    · obtain ⟨e₁⟩ := twist_one ρ
      exact ⟨e₁ ≪≫ (rationalIsoPullbackReflIso ρ).symm⟩
    · refine Equiv.ext fun ω => ?_
      change ω = 1 * rationalUnramifiedCharacterRestrict (𝟙 H) ω
      rw [rationalUnramifiedCharacterRestrict_id, one_mul]
  mul_mem' := by
    rintro σ τ ⟨c, χ, ⟨hχ⟩, rfl⟩ ⟨d, ψ, ⟨hψ⟩, rfl⟩
    refine ⟨c.trans d, χ * rationalUnramifiedCharacterRestrict c.iso.hom ψ, ?_, ?_⟩
    · obtain ⟨e₁⟩ := twist_twist (rationalUnramifiedCharacterRestrict c.iso.hom ψ) χ ρ
      obtain ⟨e₂⟩ := twist_eq (mul_comm (rationalUnramifiedCharacterRestrict c.iso.hom ψ) χ) ρ
      obtain ⟨e₃⟩ := twist_congr (rationalUnramifiedCharacterRestrict c.iso.hom ψ) ⟨hχ⟩
      obtain ⟨e₄⟩ := pullback_twist c.iso ψ ρ
      obtain ⟨e₅⟩ := pullback_congr c.iso ⟨hψ⟩
      exact ⟨e₂.symm ≪≫ e₁.symm ≪≫ e₃ ≪≫ e₄.symm ≪≫ e₅ ≪≫
        rationalIsoPullbackTransIso c.iso d.iso ρ⟩
    · refine Equiv.ext fun ω => ?_
      change χ * rationalUnramifiedCharacterRestrict c.iso.hom
          (ψ * rationalUnramifiedCharacterRestrict d.iso.hom ω) =
        χ * rationalUnramifiedCharacterRestrict c.iso.hom ψ *
          rationalUnramifiedCharacterRestrict (c.iso.hom ≫ d.iso.hom) ω
      rw [map_mul, rationalUnramifiedCharacterRestrict_comp, mul_assoc]
  inv_mem' := by
    rintro σ ⟨c, χ, ⟨hχ⟩, rfl⟩
    refine ⟨c.symm, (rationalUnramifiedCharacterRestrict c.iso.inv χ)⁻¹, ?_, ?_⟩
    · obtain ⟨e₁⟩ := pullback_congr c.iso.symm ⟨hχ⟩
      obtain ⟨e₂⟩ := pullback_twist c.iso.symm χ ρ
      have e₃ := rationalIsoPullbackCancelIso c.iso.symm ρ
      rw [Iso.symm_symm_eq] at e₃
      have h : Nonempty (rationalUnramifiedTwist H
          (rationalUnramifiedCharacterRestrict c.iso.inv χ)
          (rationalIsoPullback c.iso.symm ρ) ≅ ρ) := ⟨e₂.symm ≪≫ e₁ ≪≫ e₃⟩
      obtain ⟨e₄⟩ := (twist_iso_iff _ _ _).1 h
      exact ⟨e₄.symm⟩
    · refine Equiv.ext fun ω => ?_
      change rationalUnramifiedCharacterRestrict c.iso.inv (χ⁻¹ * ω) =
        (rationalUnramifiedCharacterRestrict c.iso.inv χ)⁻¹ *
          rationalUnramifiedCharacterRestrict c.iso.inv ω
      rw [map_mul, map_inv]

variable (j : H ⟶ G) (ρ : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H))

/-- The orbits of `W` are the classes of `ρ ⊗ ω ≅ (ρ ⊗ ω')^c`. -/
theorem assoc_iff_exists_weylGroup (ω ω' : UChar H) :
    (∃ c : RationalLeviConjugacy j j, Nonempty (rationalUnramifiedTwist H ω ρ ≅
        rationalIsoPullback c.iso (rationalUnramifiedTwist H ω' ρ))) ↔
      ∃ w ∈ weylGroup j ρ, w ω' = ω := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨affinePerm c.iso (ω * (rationalUnramifiedCharacterRestrict c.iso.hom ω')⁻¹),
      ⟨c, _, (iso_pullback_twist_iff ρ c.iso ω ω').1 hc, rfl⟩, ?_⟩
    rw [affinePerm_apply, inv_mul_cancel_right]
  · rintro ⟨w, ⟨c, χ, hχ, rfl⟩, hw⟩
    refine ⟨c, (iso_pullback_twist_iff ρ c.iso ω ω').2 ?_⟩
    rw [affinePerm_apply] at hw
    rwa [← hw, mul_inv_cancel_right]

/-- Every element of `W` preserves `ℂ[X(H)]`. -/
theorem weylGroup_comp_mem_regular {w : Equiv.Perm (UChar H)} (hw : w ∈ weylGroup j ρ)
    {f : UChar H → ℂ}
    (hf : f ∈ unramifiedRegularFunctions (fun ψ => (rationalNormCharacters H ψ).toMul)) :
    (fun ω => f (w ω)) ∈
      unramifiedRegularFunctions (fun ψ => (rationalNormCharacters H ψ).toMul) := by
  obtain ⟨c, χ, -, rfl⟩ := hw
  exact comp_affine_mem_regular c.iso.hom χ hf

/-- With a finite twist stabilizer, every twist set is finite. -/
theorem twistSet_finite
    (hS : {χ : UChar H | Nonempty (rationalUnramifiedTwist H χ ρ ≅ ρ)}.Finite) (e : H ≅ H) :
    (twistSet ρ e).Finite := by
  rcases (twistSet ρ e).eq_empty_or_nonempty with h | ⟨χ₀, ⟨h₀⟩⟩
  · rw [h]
    exact Set.finite_empty
  · apply (hS.image (· * χ₀)).subset
    rintro χ ⟨hχ⟩
    refine ⟨χ * χ₀⁻¹, ?_, inv_mul_cancel_right χ χ₀⟩
    exact (twist_iso_twist_iff χ χ₀ ρ ρ).1 ⟨hχ ≪≫ h₀.symm⟩

/-- Self-conjugacies whose points differ by a point of `H` give the same twist sets and the
same affine permutations. -/
theorem twistSet_affinePerm_eq_of_point_eq (hj : Mono j.hom.hom)
    (c c' : RationalLeviConjugacy j j) (m : GroupScheme.rationalPoints H)
    (h : c.point = c'.point * GroupScheme.rationalPoints.map j m) :
    twistSet ρ c.iso = twistSet ρ c'.iso ∧ ∀ χ, affinePerm c.iso χ = affinePerm c'.iso χ := by
  have hc := iso_hom_eq_of_point_eq hj c c' m h
  refine ⟨?_, fun χ => ?_⟩
  · have hpt : ∀ x, GroupScheme.rationalPoints.map c.iso.hom x =
        GroupScheme.rationalPoints.map c'.iso.hom m *
          GroupScheme.rationalPoints.map c'.iso.hom x *
          (GroupScheme.rationalPoints.map c'.iso.hom m)⁻¹ := by
      intro x
      rw [← map_inv, ← map_mul, ← map_mul]
      change x ≫ c.iso.hom.hom.hom = (m * x * m⁻¹) ≫ c'.iso.hom.hom.hom
      rw [hc, Grp.comp_hom_hom, ← Category.assoc]
      congr 1
      have := congrFun (congrArg DFunLike.coe (GroupScheme.rationalPoints_map_innerIso m)) x
      exact this
    obtain ⟨p⟩ := pullback_iso_of_conj c.iso c'.iso _ hpt ρ
    ext χ
    exact ⟨fun ⟨q⟩ => ⟨q ≪≫ p.symm⟩, fun ⟨q⟩ => ⟨q ≪≫ p⟩⟩
  · refine Equiv.ext fun ω => ?_
    change χ * rationalUnramifiedCharacterRestrict c.iso.hom ω =
      χ * rationalUnramifiedCharacterRestrict c'.iso.hom ω
    rw [hc, rationalUnramifiedCharacterRestrict_comp, restrict_innerIso]

/-- `W` is finite, given a closed embedding, finitely many normalizer representatives modulo
`H(F)`, and a finite twist stabilizer of `ρ`. -/
theorem weylGroup_finite (hj : Mono j.hom.hom)
    (hN : ∃ (n : ℕ) (g : Fin n → GroupScheme.rationalPoints G),
      ∀ (w : GroupScheme.rationalPoints G) (φ : H ≅ H),
        φ.hom ≫ j = j ≫ (G.innerIso w).hom →
          ∃ (t : Fin n) (m : GroupScheme.rationalPoints H),
            w = g t * GroupScheme.rationalPoints.map j m)
    (hS : {χ : UChar H | Nonempty (rationalUnramifiedTwist H χ ρ ≅ ρ)}.Finite) :
    Finite (weylGroup j ρ) := by
  obtain ⟨n, g, hg⟩ := hN
  let S : Fin n → Set (Equiv.Perm (UChar H)) := fun t =>
    {σ | ∃ c : RationalLeviConjugacy j j, ∃ χ ∈ twistSet ρ c.iso,
      σ = affinePerm c.iso χ ∧ ∃ m, c.point = g t * GroupScheme.rationalPoints.map j m}
  have hsub : (weylGroup j ρ : Set (Equiv.Perm (UChar H))) ⊆ ⋃ t, S t := by
    rintro σ ⟨c, χ, hχ, rfl⟩
    obtain ⟨t, m, hm⟩ := hg c.point c.iso c.commutes.symm
    exact Set.mem_iUnion.2 ⟨t, c, χ, hχ, rfl, m, hm⟩
  have hfin : ∀ t, (S t).Finite := by
    intro t
    rcases (S t).eq_empty_or_nonempty with h | ⟨σ₀, c₀, χ₀, -, -, m₀, hm₀⟩
    · rw [h]
      exact Set.finite_empty
    · apply ((twistSet_finite ρ hS c₀.iso).image (affinePerm c₀.iso)).subset
      rintro σ ⟨c, χ, hχ, rfl, m, hm⟩
      have hpt : c.point = c₀.point * GroupScheme.rationalPoints.map j (m₀⁻¹ * m) := by
        rw [hm, hm₀, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
      obtain ⟨h₁, h₂⟩ := twistSet_affinePerm_eq_of_point_eq j ρ hj c c₀ _ hpt
      exact ⟨χ, h₁ ▸ hχ, (h₂ χ).symm⟩
  exact ((Set.finite_iUnion hfin).subset hsub).to_subtype

end Weyl

end Langlands.CuspidalSupport.ComponentWeyl
