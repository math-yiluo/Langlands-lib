import Langlands.Representation.Induction.NormalSplitComparison
import Langlands.Representation.Induction.CoefficientSplitKernelIntegral

/-! Native coefficient normal coinvariants and split quotient comparison. -/

noncomputable section

namespace Langlands.Induction.Coefficient

open Langlands.Jacquet.CoefficientRestriction

universe uR uG uL uV uW

variable {R : Type uR} [CommRing R]

section Map

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The actual coinvariant map, bundled with its descended ambient equivariance. -/
noncomputable def normalCoinvariantsMap (N : Subgroup G) [N.Normal]
    {rho : Representation R G V} {tau : Representation R G W}
    (T : rho.IntertwiningMap tau) :
    (rho.toCoinvariants N).IntertwiningMap (tau.toCoinvariants N) where
  toLinearMap := Representation.Coinvariants.map _ _ (Jacquet.restrictMap T N)
  isIntertwining' g := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change Representation.Coinvariants.mk _ (T (rho g v)) =
      Representation.Coinvariants.mk _ (tau g (T v))
    exact congrArg (Representation.Coinvariants.mk _)
      (Representation.IntertwiningMap.isIntertwining rho tau T g v)

end Map

section Transport

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]
variable {ρ : Representation R G V} {τ : Representation R G W}

/-- Transport of actual normal coinvariants retaining the ambient action. -/
def normalCoinvariantsEquiv (N : Subgroup G) [N.Normal] (e : ρ.Equiv τ) :
    (ρ.toCoinvariants N).Equiv (τ.toCoinvariants N) where
  toLinearMap := (normalCoinvariantsMap N e.toIntertwiningMap).toLinearMap
  invFun := normalCoinvariantsMap N e.symm.toIntertwiningMap
  left_inv z := by
    induction z using Representation.Coinvariants.induction_on with
    | h v => exact congrArg (Representation.Coinvariants.mk _) (e.symm_apply_apply v)
  right_inv z := by
    induction z using Representation.Coinvariants.induction_on with
    | h v => exact congrArg (Representation.Coinvariants.mk _) (e.apply_symm_apply v)
  isIntertwining' := (normalCoinvariantsMap N e.toIntertwiningMap).isIntertwining'

@[simp] theorem normalCoinvariantsEquiv_mk (N : Subgroup G) [N.Normal]
    (e : ρ.Equiv τ) (v : V) :
    normalCoinvariantsEquiv N e (Representation.Coinvariants.mk (ρ.comp N.subtype) v) =
      Representation.Coinvariants.mk (τ.comp N.subtype) (e v) := rfl

/-- Equality of normal subgroups transports the actual quotient representation. -/
def normalCoinvariantsCongr (ρ : Representation R G V) {N K : Subgroup G}
    [N.Normal] [K.Normal] (h : N = K) :
    (ρ.toCoinvariants N).Equiv (ρ.toCoinvariants K) := by
  subst K
  exact Representation.Equiv.refl _

@[simp] theorem normalCoinvariantsCongr_mk (ρ : Representation R G V)
    {N K : Subgroup G} [N.Normal] [K.Normal] (h : N = K) (v : V) :
    normalCoinvariantsCongr ρ h (Representation.Coinvariants.mk (ρ.comp N.subtype) v) =
      Representation.Coinvariants.mk (ρ.comp K.subtype) v := by
  subst K
  rfl

/-- Restrict a representation equivalence without changing its linear map. -/
def restrictAlongEquiv {L : Type uL} [Group L] (s : L →* G) (e : ρ.Equiv τ) :
    Representation.Equiv (ρ.comp s) (τ.comp s) where
  toLinearEquiv := e.toLinearEquiv
  isIntertwining' l := e.isIntertwining' (s l)

@[simp] theorem restrictAlongEquiv_apply {L : Type uL} [Group L]
    (s : L →* G) (e : ρ.Equiv τ) (v : V) : restrictAlongEquiv s e v = e v := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Postcomposition transports actual compact induction along an equivalence. -/
def compactInducedEquiv (H : Subgroup G)
    {σ : Representation R H V} {π : Representation R H W} (e : σ.Equiv π) :
    (compactInduced H σ).Equiv (compactInduced H π) where
  toLinearMap := (compactInducedMap H e.toIntertwiningMap).toLinearMap
  invFun := compactInducedMap H e.symm.toIntertwiningMap
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact e.symm_apply_apply (eval H σ f.val g)
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact e.apply_symm_apply (eval H π f.val g)
  isIntertwining' := (compactInducedMap H e.toIntertwiningMap).isIntertwining'

@[simp] theorem compactInducedEquiv_eval (H : Subgroup G)
    {σ : Representation R H V} {π : Representation R H W} (e : σ.Equiv π)
    (f : CompactFunctions H σ) (g : G) :
    eval H π (compactInducedEquiv H e f).val g = e (eval H σ f.val g) := rfl

end Transport

section CompactNormal

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable (H N : Subgroup G) [N.Normal] (hNH : N ≤ H)
variable (σ : Representation R H V)

include hNH in
private theorem quotientPostcompose_invariant (n : N) :
    (compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H))).toLinearMap ∘ₗ
        (compactInduced H σ).comp N.subtype n =
      (compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H))).toLinearMap := by
  ext f x
  change Representation.Coinvariants.mk _ (eval H σ f.val (x * (n : G))) =
    Representation.Coinvariants.mk _ (eval H σ f.val x)
  have hn : x * (n : G) * x⁻¹ ∈ N :=
    Subgroup.Normal.conj_mem inferInstance n.val n.property x
  let p : N.subgroupOf H := ⟨⟨x * (n : G) * x⁻¹, hNH hn⟩, hn⟩
  have he : x * (n : G) = ((p.val : H) : G) * x := by
    dsimp [p]
    group
  rw [he, eval_covariant H σ f.val p.val x]
  exact Representation.Coinvariants.mk_self_apply
    (σ.comp (N.subgroupOf H).subtype) p (eval H σ f.val x)

/-- The canonical map from induced normal coinvariants to induction of coefficient coinvariants. -/
def compactNormalCoinvariantsMap :
    ((compactInduced H σ).toCoinvariants N).IntertwiningMap
      (compactInduced H (σ.toCoinvariants (N.subgroupOf H))) where
  toLinearMap := Representation.Coinvariants.lift _
    (compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H))).toLinearMap
    (quotientPostcompose_invariant H N hNH σ)
  isIntertwining' g := by
    apply Representation.Coinvariants.hom_ext
    ext f x
    rfl

theorem compactNormalCoinvariantsMap_mk (f : CompactFunctions H σ) :
    compactNormalCoinvariantsMap H N hNH σ
      (Representation.Coinvariants.mk ((compactInduced H σ).comp N.subtype) f) =
        compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H)) f := rfl

theorem compactNormalCoinvariantsMap_eval (f : CompactFunctions H σ) (g : G) :
    eval H (σ.toCoinvariants (N.subgroupOf H))
      (compactNormalCoinvariantsMap H N hNH σ
        (Representation.Coinvariants.mk ((compactInduced H σ).comp N.subtype) f)).val g =
      Representation.Coinvariants.mk (σ.comp (N.subgroupOf H).subtype)
        (eval H σ f.val g) := rfl

theorem compactNormalCoinvariantsMap_natural
    {W : Type uW} [AddCommGroup W] [Module R W]
    (τ : Representation R H W) (T : σ.IntertwiningMap τ)
    (q : Representation.Coinvariants ((compactInduced H σ).comp N.subtype)) :
    compactNormalCoinvariantsMap H N hNH τ
      (Representation.Coinvariants.map _ _
        (Jacquet.restrictMap (compactInducedMap H T) N) q) =
      compactInducedMap H (normalCoinvariantsMap (N.subgroupOf H) T)
        (compactNormalCoinvariantsMap H N hNH σ q) := by
  induction q using Representation.Coinvariants.induction_on with
  | h f => rfl


section ScalarComparison

variable [Algebra ℂ R] [Module ℂ V] [IsScalarTower ℂ R V]

/-- Complex restriction of normal coinvariants preserves the ambient operators. -/
def normalCoinvariantsComplexEquiv {K : Type*} [Group K] (N : Subgroup K) [N.Normal]
    (ρ : Representation R K V) :
    ((complexRepresentation ρ).toCoinvariants N).Equiv
      (complexRepresentation (ρ.toCoinvariants N)) where
  toLinearEquiv := fullCoinvariantsComplexEquiv (ρ.comp N.subtype)
  isIntertwining' k := by
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
    rfl

@[simp] theorem normalCoinvariantsComplexEquiv_mk {K : Type*} [Group K]
    (N : Subgroup K) [N.Normal] (ρ : Representation R K V) (v : V) :
    normalCoinvariantsComplexEquiv N ρ
      (Representation.Coinvariants.mk ((complexRepresentation ρ).comp N.subtype) v) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) v := rfl

@[simp] theorem normalCoinvariantsComplexEquiv_symm_mk {K : Type*} [Group K]
    (N : Subgroup K) [N.Normal] (ρ : Representation R K V) (v : V) :
    (normalCoinvariantsComplexEquiv N ρ).symm
      (Representation.Coinvariants.mk (ρ.comp N.subtype) v) =
      Representation.Coinvariants.mk ((complexRepresentation ρ).comp N.subtype) v := by
  apply (normalCoinvariantsComplexEquiv N ρ).toLinearEquiv.injective
  change (normalCoinvariantsComplexEquiv N ρ).toLinearEquiv
      ((normalCoinvariantsComplexEquiv N ρ).toLinearEquiv.symm
        (Representation.Coinvariants.mk (ρ.comp N.subtype) v)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The source quotient comparison retains every original compact function. -/
def compactNormalSourceComplexEquiv :
    Representation.Coinvariants ((compactInduced H σ).comp N.subtype) ≃ₗ[ℂ]
      Representation.Coinvariants ((compactInduced H (complexRepresentation σ)).comp N.subtype) :=
  (fullCoinvariantsComplexEquiv ((compactInduced H σ).comp N.subtype)).symm.trans
    (fullCoinvariantsCongr (restrictAlongEquiv N.subtype (compactInducedComplexEquiv H σ)))

omit [N.Normal] in
@[simp] theorem compactNormalSourceComplexEquiv_mk (f : CompactFunctions H σ) :
    compactNormalSourceComplexEquiv H N σ
      (Representation.Coinvariants.mk ((compactInduced H σ).comp N.subtype) f) =
      Representation.Coinvariants.mk
        ((compactInduced H (complexRepresentation σ)).comp N.subtype)
        (compactFunctionsComplexEquiv H σ f) := rfl

/-- The target comparison is pointwise the identity on original vector classes. -/
def compactNormalTargetComplexEquiv :
    CompactFunctions H (σ.toCoinvariants (N.subgroupOf H)) ≃ₗ[ℂ]
      CompactFunctions H ((complexRepresentation σ).toCoinvariants (N.subgroupOf H)) :=
  (compactFunctionsComplexEquiv H (σ.toCoinvariants (N.subgroupOf H))).trans
    (compactInducedEquiv H (normalCoinvariantsComplexEquiv (N.subgroupOf H) σ).symm).toLinearEquiv

/-- Native pointwise quotient descent is the published map on the same functions. -/
theorem compactNormalCoinvariantsMap_complex
    (z : Representation.Coinvariants ((compactInduced H σ).comp N.subtype)) :
    compactNormalTargetComplexEquiv H N σ (compactNormalCoinvariantsMap H N hNH σ z) =
      Langlands.Induction.compactNormalCoinvariantsMap H N hNH (complexRepresentation σ)
        (compactNormalSourceComplexEquiv H N σ z) := by
  obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change (normalCoinvariantsComplexEquiv (N.subgroupOf H) σ).symm
      (Representation.Coinvariants.mk (σ.comp (N.subgroupOf H).subtype) (eval H σ f.val g)) = _
  rw [normalCoinvariantsComplexEquiv_symm_mk]
  rfl

section Bijectivity

variable [T2Space G]
variable (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
variable (hH : IsClosed (H : Set G)) (hN : IsClosed (N : Set G))
variable (hσ : IsSmooth σ)

include hBasis hH hN hσ in
/-- Bijectivity of the actual native map follows through the original scalar comparisons. -/
theorem compactNormalCoinvariantsMap_bijective :
    Function.Bijective (compactNormalCoinvariantsMap H N hNH σ) := by
  let eS := compactNormalSourceComplexEquiv H N σ
  let eT := compactNormalTargetComplexEquiv H N σ
  let eC := Langlands.Induction.compactNormalCanonicalEquiv hBasis H N hH hN hNH
    (complexRepresentation σ) ((isSmooth_complexRepresentation σ).mpr hσ)
  have he : (compactNormalCoinvariantsMap H N hNH σ : _ → _) =
      eT.symm ∘ eC ∘ eS := by
    funext z
    apply eT.injective
    change eT (compactNormalCoinvariantsMap H N hNH σ z) =
      eT (eT.symm (eC (eS z)))
    rw [LinearEquiv.apply_symm_apply]
    exact compactNormalCoinvariantsMap_complex H N hNH σ z
  rw [he]
  exact eT.symm.bijective.comp (eC.bijective.comp eS.bijective)

/-- The canonical native quotient map bundled with its proved bijectivity. -/
def compactNormalCanonicalEquiv :
    Representation.Equiv ((compactInduced H σ).toCoinvariants N)
      (compactInduced H (σ.toCoinvariants (N.subgroupOf H))) :=
  (compactNormalCoinvariantsMap H N hNH σ).ofBijective
    (compactNormalCoinvariantsMap_bijective H N hNH σ hBasis hH hN hσ)

@[simp] theorem compactNormalCanonicalEquiv_mk (f : CompactFunctions H σ) :
    compactNormalCanonicalEquiv H N hNH σ hBasis hH hN hσ
        (Representation.Coinvariants.mk ((compactInduced H σ).comp N.subtype) f) =
      compactInducedMap H (σ.toCoinvariantsMkQ (N.subgroupOf H)) f := rfl

end Bijectivity
end ScalarComparison
end CompactNormal

section Split

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable [Algebra ℂ R] [Module ℂ V] [IsScalarTower ℂ R V]
variable (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
variable (r : G →* L) (s : L →* G) (hr : Continuous r) (hs : Continuous s)
variable (hrs : ∀ l, r (s l) = l) (H : Subgroup G)
variable (hH : IsClosed (H : Set G)) (hN : IsClosed (r.ker : Set G)) (hker : r.ker ≤ H)
variable (σ : Representation R H V) (hσ : IsSmooth σ)

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [TopologicalSpace L] [IsTopologicalGroup L]
  [Algebra ℂ R] [Module ℂ V] [IsScalarTower ℂ R V] in
private theorem coinvariantKernel_trivial (h : H) (hh : r (h : G) = 1)
    (z : Representation.Coinvariants (σ.comp (r.ker.subgroupOf H).subtype)) :
    σ.toCoinvariants (r.ker.subgroupOf H) h z = z := by
  induction z using Representation.Coinvariants.induction_on with
  | h v =>
    let n : r.ker.subgroupOf H := ⟨h, MonoidHom.mem_ker.mpr hh⟩
    exact Representation.Coinvariants.mk_self_apply
      (σ.comp (r.ker.subgroupOf H).subtype) n v

/-- The actual normal-coinvariant comparison, restricted to the section,
is compact induction on the split quotient. -/
def normalSplitCompactEquiv :
    Representation.Equiv (((compactInduced H σ).toCoinvariants r.ker).comp s)
      (compactInduced (H.comap s)
        ((σ.toCoinvariants (r.ker.subgroupOf H)).comp (s.subgroupComap H))) := by
  let e := compactNormalCanonicalEquiv H r.ker hker σ hBasis hH hN hσ
  let es : Representation.Equiv (((compactInduced H σ).toCoinvariants r.ker).comp s)
      ((compactInduced H (σ.toCoinvariants (r.ker.subgroupOf H))).comp s) :=
    { toLinearEquiv := e.toLinearEquiv
      isIntertwining' l := e.isIntertwining' (s l) }
  exact es.trans (splitQuotientEquiv r hr s hs hrs H hker
    (σ.toCoinvariants (r.ker.subgroupOf H)) (coinvariantKernel_trivial r H σ))

@[simp] theorem normalSplitCompactEquiv_eval_mk (f : CompactFunctions H σ) (l : L) :
    eval (H.comap s)
      ((σ.toCoinvariants (r.ker.subgroupOf H)).comp (s.subgroupComap H))
      (normalSplitCompactEquiv hBasis r s hr hs hrs H hH hN hker σ hσ
        (Representation.Coinvariants.mk ((compactInduced H σ).comp r.ker.subtype) f)).val l =
      Representation.Coinvariants.mk (σ.comp (r.ker.subgroupOf H).subtype)
        (eval H σ f.val (s l)) := rfl

/-- Naturality in every coefficient intertwiner, with independent coefficient
universes, for the same canonical split comparison. -/
theorem normalSplitCompactEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module R W] [Module ℂ W] [IsScalarTower ℂ R W]
    {τ : Representation R H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)
    (z : Representation.Coinvariants ((compactInduced H σ).comp r.ker.subtype)) :
    normalSplitCompactEquiv hBasis r s hr hs hrs H hH hN hker τ hτ
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H T) r.ker) z) =
      compactInducedMap (H.comap s)
        (restrictAlongMap (s.subgroupComap H)
          (normalCoinvariantsMap (r.ker.subgroupOf H) T))
        (normalSplitCompactEquiv hBasis r s hr hs hrs H hH hN hker σ hσ z) := by
  induction z using Representation.Coinvariants.induction_on with
  | h f =>
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext l
    rfl


end Split

end Langlands.Induction.Coefficient
