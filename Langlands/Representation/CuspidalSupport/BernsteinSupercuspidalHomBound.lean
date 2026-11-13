import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.Aubert.General.RationalInducedJacquetGeometricFiltration
import Langlands.Representation.Aubert.General.RationalFirstAdjointness
import Langlands.Representation.Aubert.General.InductionCarrierTransport
import Langlands.Representation.Filtration.IntertwiningRankFiltrationBound
import Langlands.Representation.Schur.RationalPoints
import Langlands.Representation.Schur.TwistedHom
import Langlands.Representation.Classification.CuspidalProductContragredient

/-! # The Hom bound for induction from cuspidal data (Renard VI.5.4, second bound) -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe uG uV uW uV' uW' uX u v

open CategoryTheory

namespace Langlands.CuspidalSupport.HomBound

section Generic

variable {H : Type uG} [Group H]
variable {V : Type uV} {V' : Type uV'} {W : Type uW} {W' : Type uW'}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/-- Representation equivalences of source and target identify the intertwiner
spaces linearly: `f ↦ e₂ ∘ f ∘ e₁⁻¹`. -/
def intertwiningMapLinearCongr {ρ : Representation ℂ H V} {ρ' : Representation ℂ H V'}
    {τ : Representation ℂ H W} {τ' : Representation ℂ H W'}
    (e₁ : ρ.Equiv ρ') (e₂ : τ.Equiv τ') :
    ρ.IntertwiningMap τ ≃ₗ[ℂ] ρ'.IntertwiningMap τ' where
  toFun f := e₂.toIntertwiningMap.comp (f.comp e₁.symm.toIntertwiningMap)
  invFun f := e₂.symm.toIntertwiningMap.comp (f.comp e₁.toIntertwiningMap)
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change e₂.symm (e₂ (f (e₁.symm (e₁ x)))) = f x
    rw [Representation.Equiv.symm_apply_apply, Representation.Equiv.symm_apply_apply]
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change e₂ (e₂.symm (f (e₁ (e₁.symm x)))) = f x
    rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply]
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact map_add e₂ (f (e₁.symm x)) (g (e₁.symm x))
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact map_smul e₂ c (f (e₁.symm x))

/-- A vanishing intertwiner space has rank zero. -/
theorem rank_le_zero_of_forall_eq_zero {ρ : Representation ℂ H V} {τ : Representation ℂ H W}
    (h : ∀ f : ρ.IntertwiningMap τ, f = 0) (c : Cardinal) :
    Module.rank ℂ (ρ.IntertwiningMap τ) ≤ c := by
  have : Subsingleton (ρ.IntertwiningMap τ) := ⟨fun f g => (h f).trans (h g).symm⟩
  rw [rank_subsingleton']
  exact zero_le

/-- Isomorphic sources satisfy the same intertwiner rank bound. -/
theorem rank_intertwiningMap_le_of_iso {A B : Rep.{uV} ℂ H} (e : A ≅ B)
    {τ : Representation ℂ H W} {c : Cardinal}
    (h : Module.rank ℂ (B.ρ.IntertwiningMap τ) ≤ c) :
    Module.rank ℂ (A.ρ.IntertwiningMap τ) ≤ c := by
  rw [(intertwiningMapLinearCongr (Representation.equivOfIso e)
    (Representation.Equiv.refl τ)).rank_eq]
  exact h

/-- Membership `x ∈ L' ↔ g⁻¹ x g ∈ L` says exactly that `g L g⁻¹ = L'`. -/
theorem map_conj_eq_of_forall_mem_iff {L L' : Subgroup H} (g : H)
    (hg : ∀ x : H, x ∈ L' ↔ g⁻¹ * x * g ∈ L) :
    L.map (MulAut.conj g : H →* H) = L' := by
  ext x
  rw [Subgroup.mem_map, hg x]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

end Generic

section Count

/-- Summing the indicator of `P` along an enumeration of `{w // Q w}` counts
the elements satisfying both `Q` and `P`. -/
theorem sum_ite_enumeration_eq_card {α : Type uG} {Q : α → Prop} {n : ℕ}
    (e : Fin n ≃ {w // Q w}) (P : α → Prop) [DecidablePred P] :
    (∑ q, if P (e q).val then 1 else 0 : ℕ) = Nat.card {w // Q w ∧ P w} := by
  rw [Finset.sum_boole, Nat.cast_id, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr ((e.subtypeEquiv (fun _ => Iff.rfl)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter Q P))

end Count

section Schur

variable {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace.SeparableSpace H]
variable {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Between a smooth irreducible representation of a separable group and any
irreducible representation there is at most one independent intertwiner. -/
theorem rank_intertwiningMap_le_one
    (ρ : Representation ℂ H V) (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (τ : Representation ℂ H W) (hτ : τ.IsIrreducible) :
    Module.rank ℂ (ρ.IntertwiningMap τ) ≤ 1 := by
  classical
  by_cases hz : ∀ f : ρ.IntertwiningMap τ, f = 0
  · have : Subsingleton (ρ.IntertwiningMap τ) :=
      ⟨fun f g => (hz f).trans (hz g).symm⟩
    rw [rank_subsingleton']
    exact zero_le_one
  · push Not at hz
    obtain ⟨f, hf⟩ := hz
    have : ρ.IsIrreducible := hi
    have : τ.IsIrreducible := hτ
    let e := f.ofBijective
      ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)
    have h := ((Schur.intertwiningMapEquivEnd e).trans
      (Schur.separableSmoothEndomorphismEquiv ρ hρ hi).symm).lift_rank_eq
    rw [Module.rank_self, Cardinal.lift_one] at h
    exact Cardinal.lift_le_one_iff.mp h.le

end Schur

section Subquotient

variable {H : Type uG} [Group H] [TopologicalSpace H]

/-- A nonzero intertwiner onto an irreducible representation exhibits it as a
quotient, hence as a subquotient. -/
theorem intertwiningMap_eq_zero_of_not_isSubquotient
    {X τ : SmoothRep.{0, uG, uV} ℂ H} (hτ : τ.IsIrreducible)
    (hX : ¬ SmoothRep.IsSubquotient τ X)
    (f : X.representation.IntertwiningMap τ.representation) : f = 0 := by
  by_contra hf
  have : τ.representation.IsIrreducible := hτ
  have hs : Function.Surjective f :=
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  exact hX (Classification.CuspidalProductContragredient.isSubquotient_of_injective_of_surjective (𝟙 τ) (fun _ _ h => h)
    (SmoothRep.ofHom f) hs)

end Subquotient

section Dichotomy

variable {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace.SeparableSpace H]

/-- Rank bound for intertwiners out of a representation `X` into an irreducible
`τ`, when either `τ` is not a subquotient of `X`, or `X` is isomorphic to an
irreducible `Y` such that every isomorphism `Y ≅ τ` forces the proposition `p`:
the rank is at most `1` if `p` holds and `0` otherwise. -/
theorem rank_intertwiningMap_le_ite
    {X τ : SmoothRep.{0, uG, uV} ℂ H} (hτ : τ.IsIrreducible) (p : Prop) [Decidable p]
    (h : ¬ SmoothRep.IsSubquotient τ X ∨
      ∃ Y : SmoothRep.{0, uG, uV} ℂ H, Y.IsIrreducible ∧ Nonempty (X ≅ Y) ∧
        (Nonempty (Y ≅ τ) → p)) :
    Module.rank ℂ (X.representation.IntertwiningMap τ.representation) ≤
      ((if p then 1 else 0 : ℕ) : Cardinal) := by
  rcases h with hX | ⟨Y, hY, ⟨e⟩, hp⟩
  · exact rank_le_zero_of_forall_eq_zero
      (fun f => intertwiningMap_eq_zero_of_not_isSubquotient hτ hX f) _
  · rw [(intertwiningMapLinearCongr (SmoothRep.equivOfIso e)
      (Representation.Equiv.refl τ.representation)).rank_eq]
    by_cases hpw : p
    · simp only [hpw, ↓reduceIte, Nat.cast_one]
      exact rank_intertwiningMap_le_one Y.representation Y.isSmooth hY τ.representation hτ
    · simp only [hpw, ↓reduceIte, Nat.cast_zero]
      refine rank_le_zero_of_forall_eq_zero (fun f => ?_) _
      by_contra hf
      have : Y.representation.IsIrreducible := hY
      have : τ.representation.IsIrreducible := hτ
      exact hpw (hp ⟨SmoothRep.mkIso (f.ofBijective
        ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf))⟩)

end Dichotomy

section Conjugate

variable {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Conjugate form of `rank_intertwiningMap_le_ite`: the comparison object is
the conjugate of an irreducible `σ` along `g`. -/
theorem rank_intertwiningMap_le_ite_of_conjugate {L M : Subgroup H}
    [TopologicalSpace.SeparableSpace M]
    (g : H) (hg : ∀ x : H, x ∈ M ↔ g⁻¹ * x * g ∈ L)
    {σ : SmoothRep.{0, uG, uV} ℂ L} (hσ : σ.IsIrreducible)
    {X τ : SmoothRep.{0, uG, uV} ℂ M} (hτ : τ.IsIrreducible) (p : Prop) [Decidable p]
    (h : ¬ SmoothRep.IsSubquotient τ X ∨
      Nonempty (X ≅ (Aubert.General.conjugationFunctor g hg).obj σ))
    (hp : Nonempty ((Aubert.General.conjugationFunctor g hg).obj σ ≅ τ) → p) :
    Module.rank ℂ (X.representation.IntertwiningMap τ.representation) ≤
      ((if p then 1 else 0 : ℕ) : Cardinal) := by
  refine rank_intertwiningMap_le_ite hτ p ?_
  rcases h with hX | he
  · exact Or.inl hX
  · have hY : ((Aubert.General.conjugationFunctor g hg).obj σ).IsIrreducible :=
      (Langlands.isIrreducible_comp_continuousMulEquiv_iff
        σ.representation (Aubert.General.conjugationEquiv g hg)).mpr hσ
    exact Or.inr ⟨_, hY, he, hp⟩

/-- Conjugating by `g` and then by `g⁻¹` is the identity on `L`. -/
theorem conjugationEquiv_relativeWeylConjugationEquiv {L L' : Subgroup H} (g : H)
    (hg : ∀ x : H, x ∈ L' ↔ g⁻¹ * x * g ∈ L) (m : L) :
    Aubert.General.conjugationEquiv g hg
      (Group.RelativeWeyl.conjugationEquiv g L L' (map_conj_eq_of_forall_mem_iff g hg) m) = m := by
  apply Subtype.ext
  simp [mul_assoc]

/-- An isomorphism `ᵍ(A↑) ≅ B↑` between universe lifts, along `g` with
`g⁻¹ L' g = L`, gives `g L g⁻¹ = L'` together with a linear equivalence
`e : A ≃ B` satisfying `e (A m x) = B (g m g⁻¹) (e x)` for `m ∈ L`. -/
theorem exists_conjugation_linearEquiv_of_iso_universeLift {L L' : Subgroup H} (g : H)
    (hg : ∀ x : H, x ∈ L' ↔ g⁻¹ * x * g ∈ L)
    {A : SmoothRep.{0, uG, uV} ℂ L} {B : SmoothRep.{0, uG, uV} ℂ L'}
    (φ : (Aubert.General.conjugationFunctor g hg).obj (SmoothRep.universeLift.{uX} A) ≅
      SmoothRep.universeLift.{uX} B) :
    ∃ h : L.map (MulAut.conj g : H →* H) = L',
      ∃ e : A ≃ₗ[ℂ] B, ∀ (m : L) (x : A),
        e (A.representation m x) =
          B.representation (Group.RelativeWeyl.conjugationEquiv g L L' h m) (e x) := by
  refine ⟨map_conj_eq_of_forall_mem_iff g hg, ?_⟩
  let E := SmoothRep.equivOfIso φ
  let e : A ≃ₗ[ℂ] B :=
    ((SmoothRep.universeLiftEquiv.{uX} A).toLinearEquiv.trans E.toLinearEquiv).trans
      (SmoothRep.universeLiftEquiv.{uX} B).symm.toLinearEquiv
  have he : ∀ x : A, e x = (E (ULift.up x)).down := fun x => rfl
  refine ⟨e, fun m x => ?_⟩
  rw [he, he]
  have hI := LinearMap.congr_fun (E.isIntertwining'
    (Group.RelativeWeyl.conjugationEquiv g L L' (map_conj_eq_of_forall_mem_iff g hg) m))
    (ULift.up x)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hI
  have h1 : ((Aubert.General.conjugationFunctor g hg).obj
      (SmoothRep.universeLift.{uX} A)).representation
        (Group.RelativeWeyl.conjugationEquiv g L L' (map_conj_eq_of_forall_mem_iff g hg) m)
        (ULift.up x) = ULift.up (A.representation m x) := by
    rw [Aubert.General.conjugationFunctor_obj_apply,
      conjugationEquiv_relativeWeylConjugationEquiv]
    rfl
  rw [h1] at hI
  change E (ULift.up (A.representation m x)) = _ at hI
  rw [hI]
  rfl

end Conjugate

section Rational

open _root_.AlgebraicGeometry GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) C)
  [TopologicalSpace k] (hStandard : StandardCocharacterStatement.{u})

local instance homBoundPointTopology : TopologicalSpace (RationalPoint k G.X) :=
  pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

set_option maxHeartbeats 200000 in
omit [Fintype (SimpleRoot i ν)] in
open Classical in
/-- One actual geometric grade of `r_J i_I σ` has at most one independent
intertwiner to an irreducible cuspidal `τ`, and none unless `τ` is the
conjugate of `σ` along a lift of the grade's minimal representative. -/
theorem rank_geometricTerm_intertwiningMap_le
    [SecondCountableTopology (RationalPoint k G.X)]
    (hD : PointGeometricCuspidalGradeDichotomy.{u, v}
      i ν hN hZ cs hInter hG hi hν hM hU)
    {I J : Finset (SimpleRoot i ν)}
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)) (hσ : σ.IsIrreducible)
    (hcσ : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I (hM I) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ)
    (τ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) (hτ : τ.IsIrreducible)
    (hcτ : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU J (hM J) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) τ)
    (P : Weyl i → Prop)
    (hP : ∀ (n : Group.RelativeWeyl.normalizer (torusPoints i))
      (hn : ∀ x : RationalPoint k G.X, x ∈ levi i ν J ↔
        (n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X) ∈ levi i ν I),
      Nonempty ((conjugationFunctor (n : RationalPoint k G.X) hn).obj σ ≅ τ) →
        P (QuotientGroup.mk n))
    (w : Weyl i) (hw : IsMinimal cs J I w)
    (m : Group.RelativeWeyl.normalizer (torusPoints i)) (hm : QuotientGroup.mk m = w)
    (hs : GeometricSourceDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J I m)
    (ht : GeometricTargetDecomposition (parabolic i ν) (levi i ν) (unipotent i ν) J I m) :
    Module.rank ℂ (((geometricTermFunctor.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I m hs ht).obj
          σ).representation.IntertwiningMap τ.representation) ≤
      ((if P w then 1 else 0 : ℕ) : Cardinal) := by
  subst hm
  have : SecondCountableTopology (levi i ν J) :=
    TopologicalSpace.Subtype.secondCountableTopology (levi i ν J : Set (RationalPoint k G.X))
  rcases hD I J _ hw m rfl hs ht σ hcσ with hno | ⟨hn, -, he⟩
  · exact rank_intertwiningMap_le_ite hτ _ (Or.inl (hno τ hτ hcτ))
  · exact rank_intertwiningMap_le_ite_of_conjugate _ hn hσ hτ _ (Or.inr he) (hP m hn)

set_option maxHeartbeats 200000 in
omit [Fintype (SimpleRoot i ν)] in
open Classical in
/-- Summing the per-grade bound over the actual geometric filtration of
`r_J i_I σ`: intertwiners to an irreducible cuspidal `τ` number at most the
minimal representatives `w` satisfying `P`. -/
theorem rank_pointInducedJacquet_intertwiningMap_le [Fintype (Weyl i)]
    [SecondCountableTopology (RationalPoint k G.X)]
    (hD : PointGeometricCuspidalGradeDichotomy.{u, v}
      i ν hN hZ cs hInter hG hi hν hM hU)
    {I J : Finset (SimpleRoot i ν)}
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)) (hσ : σ.IsIrreducible)
    (hcσ : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I (hM I) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ)
    (τ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) (hτ : τ.IsIrreducible)
    (hcτ : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU J (hM J) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) τ)
    (P : Weyl i → Prop)
    (hP : ∀ (n : Group.RelativeWeyl.normalizer (torusPoints i))
      (hn : ∀ x : RationalPoint k G.X, x ∈ levi i ν J ↔
        (n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X) ∈ levi i ν I),
      Nonempty ((conjugationFunctor (n : RationalPoint k G.X) hn).obj σ ≅ τ) →
        P (QuotientGroup.mk n))
    (D : PointGeometricObjectFiltration.{u, v} i ν hG hi hν hStandard hM hU cs J I σ) :
    Module.rank ℂ ((pointInducedJacquetObject.{u, v} i ν hG hi hν hStandard hU J I
        σ).representation.IntertwiningMap τ.representation) ≤
      ((Nat.card {w : Weyl i // IsMinimal cs J I w ∧ P w} : ℕ) : Cardinal) := by
  have h := D.filtration.rank_intertwiningMap_le_sum τ.representation
    (fun q => if P (D.enumeration q).val then 1 else 0)
    (fun q => rank_intertwiningMap_le_of_iso (D.grade q)
      (rank_geometricTerm_intertwiningMap_le i ν hN hZ cs hInter hG hi hν hM hU hD
        σ hσ hcσ τ hτ hcτ P hP _ ((mem_minimalReps cs J I _).mp (D.enumeration q).property)
        (D.lift q) (D.lift_class q) (D.source q) (D.target q)))
  rw [sum_ite_enumeration_eq_card D.enumeration P] at h
  refine h.trans (le_of_eq ?_)
  exact congrArg Nat.cast (Nat.card_congr (Equiv.subtypeEquivRight
    fun w => and_congr_left' (mem_minimalReps cs J I w)))

set_option maxHeartbeats 400000 in
open Classical in
/-- First adjointness turns intertwiners `i_I σ → i_J τ` into intertwiners
`r_J i_I σ → τ`; with the proper-standard exclusion input, they number at
most the minimal representatives `w` of `W_J \ W / W_I` satisfying `P`. -/
theorem rank_normalizedInduction_intertwiningMap_le
    [ValuativeRel k] [IsNonarchimedeanLocalField k]
    [T2Space (RationalPoint k G.X)] [Fintype (Weyl i)]
    (hRoots : HasRelativeRootSystem i)
    (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
    (hLength : RootLengthComparison i ν hN hZ cs)
    (hExclude : PointLeviStandardInductionCuspidalExclusion.{u, v}
      i ν hInter hG hi hν hM hU)
    {I J : Finset (SimpleRoot i ν)}
    (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)) (hσ : σ.IsIrreducible)
    (hcσ : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I (hM I) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν I) σ)
    (τ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)) (hτ : τ.IsIrreducible)
    (hcτ : Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU J (hM J) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) τ)
    (P : Weyl i → Prop)
    (hP : ∀ (n : Group.RelativeWeyl.normalizer (torusPoints i))
      (hn : ∀ x : RationalPoint k G.X, x ∈ levi i ν J ↔
        (n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X) ∈ levi i ν I),
      Nonempty ((conjugationFunctor (n : RationalPoint k G.X) hn).obj σ ≅ τ) →
        P (QuotientGroup.mk n)) :
    Module.rank ℂ (((normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
        (hU I)).obj σ).representation.IntertwiningMap
      ((normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
        (hU J)).obj τ).representation) ≤
      ((Nat.card {w : Weyl i // IsMinimal cs J I w ∧ P w} : ℕ) : Cardinal) := by
  have : SecondCountableTopology (RationalPoint k G.X) :=
    reductiveRationalPoint_secondCountable k G hG
  have hSimple := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ cs hi.isSplitSubtorus.1 hRoots hν hLength
  have hGeom := pointCuspidalExtractionGeometry_of_rootComparisons.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hStandard hInter hM hU
  have hProper := pointProperTargetGeometricTermExclusion_of_standardInduction.{u, v}
    i ν cs hGeom.1 hInter hG hi hν hM hU hExclude
  have hD := pointGeometricCuspidalGradeDichotomy_of_geometry_exclusion
    i ν hN hZ cs hInter hG hi hν hM hU hGeom hProper
  let hPc := isClosed_standard_parabolic i ν hStandard hG hi hν
  let hproj := continuous_standard_projection i ν hStandard hG hi hν
  let D := pointGeometricObjectFiltrationOfEpsilonBalance.{u, v}
    i ν hG hi hν hStandard hN hZ cs hIdent hM hU hInter hLength hSimple J I
    (fun _ _ n _ => geometricEpsilon_mul_eq_one i ν hStandard hG hi hν hN hRoots J I _ _ n
      hU hPc hM (hproj J) (hproj I)) σ
  rw [(FirstAdjointness.equiv i ν hStandard hG hi hν J (hU J)
    ((normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)).obj σ) τ).rank_eq]
  exact rank_pointInducedJacquet_intertwiningMap_le i ν hN hZ cs hStandard hInter hG hi hν hM hU
    hD σ hσ hcσ τ hτ hcτ P hP D

end Rational



end Langlands.CuspidalSupport.HomBound
