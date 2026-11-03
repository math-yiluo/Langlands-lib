import Langlands.Representation.Induction.SplitQuotientProof

/-! Smooth induction across a continuous split quotient, including inflation. -/

noncomputable section

namespace Langlands.Induction

universe uR uG uL uV uW

variable {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]

/-- Precompose a smooth induced function by a continuous section. -/
def smoothSplitQuotientRestrict (s : L →* G) (hs : Continuous s)
    (H : Subgroup G) (σ : Representation R H V) (f : SmoothFunctions H σ) :
    SmoothFunctions (H.comap s) (σ.comp (s.subgroupComap H)) :=
  smoothFunctionOf (H.comap s) (σ.comp (s.subgroupComap H))
    (fun l => eval H σ f (s l))
    (fun p l => by
      change f.1.1 (s ((p : L) * l)) = σ (s.subgroupComap H p) (f.1.1 (s l))
      rw [map_mul s]
      exact f.1.property (s.subgroupComap H p) (s l))
    ((Classical.choose f.property).comap s hs)
    (fun y l => by
      have hy := congrArg (fun F : EquivariantFunctions H σ => F.1 (s l))
        (Classical.choose_spec f.property ⟨s y, y.property⟩)
      change f.1.1 (s (l * y)) = f.1.1 (s l)
      rw [map_mul s]
      exact hy)

/-- Precompose by the retraction when the inducing coefficients are
trivial on the kernel. -/
def smoothSplitQuotientExtend (r : G →* L) (hr : Continuous r)
    (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V)
    (hσ : ∀ h : H, r (h : G) = 1 → ∀ v : V, σ h v = v)
    (k : SmoothFunctions (H.comap s) (σ.comp (s.subgroupComap H))) :
    SmoothFunctions H σ :=
  smoothFunctionOf H σ (fun g => eval (H.comap s) (σ.comp (s.subgroupComap H)) k (r g))
    (fun h x => by
      change k.1.1 (r ((h : G) * x)) = σ h (k.1.1 (r x))
      rw [map_mul r, ← splitQuotient_action_retract r s hrs H hker σ hσ h]
      exact k.1.property (splitQuotientRetract r s hrs H hker h) (r x))
    ((Classical.choose k.property).comap r hr)
    (fun y x => by
      have hy := congrArg
        (fun F : EquivariantFunctions (H.comap s) (σ.comp (s.subgroupComap H)) => F.1 (r x))
        (Classical.choose_spec k.property ⟨r y, y.property⟩)
      change k.1.1 (r (x * y)) = k.1.1 (r x)
      rw [map_mul r]
      exact hy)

/-- Smooth induction on `G` equals inflation along `r` of induction on the
split quotient `L`, for kernel-trivial inducing coefficients. -/
def smoothSplitQuotientEquiv (r : G →* L) (hr : Continuous r)
    (s : L →* G) (hs : Continuous s) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V)
    (hσ : ∀ h : H, r (h : G) = 1 → ∀ v : V, σ h v = v) :
    Representation.Equiv (smoothInduced H σ)
      ((smoothInduced (H.comap s) (σ.comp (s.subgroupComap H))).comp r) where
  toLinearMap :=
    { toFun := smoothSplitQuotientRestrict s hs H σ
      map_add' f g := by
        apply Subtype.ext
        apply Subtype.ext
        funext l
        rfl
      map_smul' c f := by
        apply Subtype.ext
        apply Subtype.ext
        funext l
        rfl }
  invFun := smoothSplitQuotientExtend r hr s hrs H hker σ hσ
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact splitQuotient_apply_section r s hrs H hker σ hσ f.1.1 f.1.property g
  right_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    funext l
    change k.1.1 (r (s l)) = k.1.1 l
    rw [hrs]
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext l
    change f.1.1 (s l * g) = f.1.1 (s (l * r g))
    have he := splitQuotient_apply_section r s hrs H hker σ hσ
      f.1.1 f.1.property (s l * g)
    simpa only [map_mul, hrs] using he.symm

@[simp] theorem smoothSplitQuotientEquiv_eval (r : G →* L) (hr : Continuous r)
    (s : L →* G) (hs : Continuous s) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V)
    (hσ : ∀ h : H, r (h : G) = 1 → ∀ v : V, σ h v = v)
    (f : SmoothFunctions H σ) (l : L) :
    eval (H.comap s) (σ.comp (s.subgroupComap H))
        (smoothSplitQuotientEquiv r hr s hs hrs H hker σ hσ f) l =
      eval H σ f (s l) := rfl

@[simp] theorem smoothSplitQuotientEquiv_symm_eval (r : G →* L) (hr : Continuous r)
    (s : L →* G) (hs : Continuous s) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V)
    (hσ : ∀ h : H, r (h : G) = 1 → ∀ v : V, σ h v = v)
    (k : SmoothFunctions (H.comap s) (σ.comp (s.subgroupComap H))) (g : G) :
    eval H σ ((smoothSplitQuotientEquiv r hr s hs hrs H hker σ hσ).symm k) g =
      eval (H.comap s) (σ.comp (s.subgroupComap H)) k (r g) := rfl

variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- The split-quotient comparison commutes with every coefficient intertwiner. -/
theorem smoothSplitQuotientEquiv_natural (r : G →* L) (hr : Continuous r)
    (s : L →* G) (hs : Continuous s) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H)
    (σ : Representation R H V) (τ : Representation R H W)
    (hσ : ∀ h : H, r (h : G) = 1 → ∀ v : V, σ h v = v)
    (hτ : ∀ h : H, r (h : G) = 1 → ∀ w : W, τ h w = w)
    (T : σ.IntertwiningMap τ) (f : SmoothFunctions H σ) :
    smoothSplitQuotientEquiv r hr s hs hrs H hker τ hτ (smoothInducedMap H T f) =
      smoothInducedMap (H.comap s) (restrictAlongMap (s.subgroupComap H) T)
        (smoothSplitQuotientEquiv r hr s hs hrs H hker σ hσ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext l
  rfl

end Langlands.Induction
