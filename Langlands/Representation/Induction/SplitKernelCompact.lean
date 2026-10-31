import Langlands.Analysis.Local.SplitKernelQuotient
import Langlands.Representation.Induction.CompactLocallyConstant

/-!
# Compact induction restricted to a split kernel

Restriction to the actual kernel is inverted using the coefficient action of
the section coordinate. Compactness is transported on actual left quotients.
-/

noncomputable section

open Filter Topology

namespace Langlands.Induction

open QuotientIntegration

universe uR uG uL uV uW

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] {L : Type uL} [Group L]
variable {V : Type uV} [AddCommGroup V] [Module R V]

/-- The section with its actual values lifted into the inducing subgroup. -/
def splitKernelSection (s : L →* G) (H : Subgroup G) (hsH : ∀ l, s l ∈ H) :
    L →* H where
  toFun l := ⟨s l, hsH l⟩
  map_one' := Subtype.ext (map_one s)
  map_mul' x y := Subtype.ext (map_mul s x y)

@[simp] theorem coe_splitKernelSection (s : L →* G) (H : Subgroup G)
    (hsH : ∀ l, s l ∈ H) (l : L) :
    (splitKernelSection s H hsH l : G) = s l := rfl

/-- Covariance recovers a function from its values on the kernel. -/
theorem splitKernel_apply_eq (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (f : G → V)
    (hf : ∀ (h : H) (g : G), f ((h : G) * g) = σ h (f g)) (g : G) :
    f g = σ (splitKernelSection s H hsH (r g))
      (f (splitKernelCoordinate r s hrs g : G)) := by
  rw [← hf]
  rw [coe_splitKernelSection, section_mul_splitKernelCoordinate]

/-- The raw extension with the section's actual coefficient action. -/
def splitKernelExtendFunction (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (k : r.ker → V) (g : G) : V :=
  σ (splitKernelSection s H hsH (r g)) (k (splitKernelCoordinate r s hrs g))

@[simp] theorem splitKernelExtendFunction_coe (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (k : r.ker → V) (n : r.ker) :
    splitKernelExtendFunction r s hrs H hsH σ k (n : G) = k n := by
  have hn : r (n : G) = 1 := n.property
  simp [splitKernelExtendFunction, hn]

/-- The coefficient action is invertible, so extension has precisely the
nonzero support of the kernel-coordinate function. -/
theorem splitKernelExtendFunction_ne_zero (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (k : r.ker → V) (g : G) :
    splitKernelExtendFunction r s hrs H hsH σ k g ≠ 0 ↔
      k (splitKernelCoordinate r s hrs g) ≠ 0 := by
  exact (σ.apply_bijective _).injective.ne_iff' (map_zero _)

/-- The raw extension is covariant under the entire inducing subgroup. -/
theorem splitKernelExtendFunction_covariant (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (k : r.ker → V)
    (hk : ∀ (i : H.comap r.ker.subtype) (n : r.ker),
      k ((i : r.ker) * n) = σ (r.ker.subtype.subgroupComap H i) (k n))
    (h : H) (g : G) :
    splitKernelExtendFunction r s hrs H hsH σ k ((h : G) * g) =
      σ h (splitKernelExtendFunction r s hrs H hsH σ k g) := by
  let a := splitKernelSection s H hsH (r ((h : G) * g))
  let b := splitKernelSection s H hsH (r g)
  let p : H := a⁻¹ * h * b
  have hp : r (p : G) = 1 := by
    change r ((s (r ((h : G) * g)))⁻¹ * (h : G) * s (r g)) = 1
    rw [map_mul, map_mul, map_inv, hrs, hrs, map_mul]
    simp [mul_inv_rev, mul_assoc]
  let i : H.comap r.ker.subtype := ⟨⟨(p : G), hp⟩, p.property⟩
  have he : splitKernelCoordinate r s hrs ((h : G) * g) =
      (i : r.ker) * splitKernelCoordinate r s hrs g := by
    apply Subtype.ext
    change (s (r ((h : G) * g)))⁻¹ * ((h : G) * g) =
      ((s (r ((h : G) * g)))⁻¹ * (h : G) * s (r g)) * ((s (r g))⁻¹ * g)
    simp [mul_assoc]
  change σ a (k (splitKernelCoordinate r s hrs ((h : G) * g))) =
    σ h (σ b (k (splitKernelCoordinate r s hrs g)))
  rw [he, hk]
  change σ a (σ p (k (splitKernelCoordinate r s hrs g))) = _
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  have hab : a * p = h * b := by simp only [p, mul_assoc, mul_inv_cancel_left]
  rw [hab]

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace L]

omit [IsTopologicalGroup G] in
/-- The lifted section has its actual subgroup topology. -/
theorem continuous_splitKernelSection (s : L →* G) (H : Subgroup G)
    (hsH : ∀ l, s l ∈ H) (hs : Continuous s) :
    Continuous (splitKernelSection s H hsH) :=
  hs.subtype_mk _

/-- Smoothness makes each individual coefficient orbit locally constant;
no topology on the coefficient module is needed. -/
theorem splitKernel_coefficient_isLocallyConstant (H : Subgroup G)
    (σ : Representation R H V) (hσ : IsSmooth σ) (v : V) :
    IsLocallyConstant (fun h : H => σ h v) := by
  obtain ⟨K, hK⟩ := hσ v
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro h
  refine ⟨(fun k : H => h * k) '' (K : Set H),
    isOpenMap_mul_left h _ K.isOpen, ⟨1, K.one_mem, mul_one h⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hv : σ k v = v := hK ⟨k, hk⟩
  rw [map_mul, Module.End.mul_apply, hv]

/-- Local constancy of extension follows from local constancy of the kernel
function and the smooth orbit of its value at the chosen point. -/
theorem splitKernelExtendFunction_isLocallyConstant (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (hσ : IsSmooth σ) (k : r.ker → V)
    (hk : IsLocallyConstant k) :
    IsLocallyConstant (splitKernelExtendFunction r s hrs H hsH σ k) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  have hkc := hk.comp_continuous (continuous_splitKernelCoordinate r s hrs hr hs)
  have hac := (splitKernel_coefficient_isLocallyConstant H σ hσ
    (k (splitKernelCoordinate r s hrs g))).comp_continuous
      ((continuous_splitKernelSection s H hsH hs).comp hr)
  filter_upwards [hkc.eventually_eq g, hac.eventually_eq g] with x hx ha
  change k (splitKernelCoordinate r s hrs x) = k (splitKernelCoordinate r s hrs g) at hx
  change σ (splitKernelSection s H hsH (r x)) (k (splitKernelCoordinate r s hrs x)) =
    σ (splitKernelSection s H hsH (r g)) (k (splitKernelCoordinate r s hrs g))
  rw [hx]
  exact ha

/-- Restriction transports actual quotient support by the inverse of the
split-kernel quotient homeomorphism. -/
theorem quotientSupport_splitKernel_restrict (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (f : G → V)
    (hf : ∀ (h : H) (g : G), f ((h : G) * g) = σ h (f g)) :
    quotientSupport (H.comap r.ker.subtype) (fun n : r.ker => f (n : G)) =
      (splitKernelLeftQuotientHomeomorph r s hrs hr hs H hsH).symm ''
        quotientSupport H f := by
  ext q
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨quotientMap H (n : G), ⟨(n : G), hn, rfl⟩, ?_⟩
    change quotientMap (H.comap r.ker.subtype) (splitKernelCoordinate r s hrs (n : G)) =
      quotientMap (H.comap r.ker.subtype) n
    rw [splitKernelCoordinate_coe]
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨splitKernelCoordinate r s hrs g, ?_, rfl⟩
    intro hn
    change f (splitKernelCoordinate r s hrs g : G) = 0 at hn
    apply hg
    rw [splitKernel_apply_eq r s hrs H hsH σ f hf g, hn, map_zero]

/-- Extension transports actual quotient support by the forward
split-kernel quotient homeomorphism. -/
theorem quotientSupport_splitKernel_extend (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (k : r.ker → V) :
    quotientSupport H (splitKernelExtendFunction r s hrs H hsH σ k) =
      splitKernelLeftQuotientHomeomorph r s hrs hr hs H hsH ''
        quotientSupport (H.comap r.ker.subtype) k := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨quotientMap (H.comap r.ker.subtype) (splitKernelCoordinate r s hrs g),
      ⟨splitKernelCoordinate r s hrs g,
        (splitKernelExtendFunction_ne_zero r s hrs H hsH σ k g).mp hg, rfl⟩, ?_⟩
    exact (splitKernelLeftQuotientHomeomorph r s hrs hr hs H hsH).apply_symm_apply
      (quotientMap H g)
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨(n : G), ?_, rfl⟩
    change splitKernelExtendFunction r s hrs H hsH σ k (n : G) ≠ 0
    change k n ≠ 0 at hn
    simpa only [splitKernelExtendFunction_coe] using hn

/-- The restriction of a compact-induced function has compact actual projected
nonzero support in the kernel quotient. -/
theorem isCompact_quotientSupport_splitKernel_restrict (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (f : CompactFunctions H σ) :
    IsCompact (quotientSupport (H.comap r.ker.subtype)
      (fun n : r.ker => eval H σ f.1 (n : G))) := by
  change IsCompact (quotientSupport (H.comap r.ker.subtype)
    (fun n : r.ker => f.1.1.1 (n : G)))
  rw [quotientSupport_splitKernel_restrict r s hrs hr hs H hsH σ
    f.1.1.1 f.1.1.property]
  exact f.2.image (splitKernelLeftQuotientHomeomorph r s hrs hr hs H hsH).symm.continuous

omit [IsTopologicalGroup G] [TopologicalSpace L] in
/-- The restriction has a uniform open right stabilizer in the actual kernel:
the open stabilizer of the smooth function, pulled back along the kernel
inclusion. -/
theorem exists_openSubgroup_splitKernel_restrict (r : G →* L) (H : Subgroup G)
    (σ : Representation R H V) (f : SmoothFunctions H σ) :
    ∃ K : OpenSubgroup r.ker, ∀ (y : K) (n : r.ker),
      eval H σ f ((n * (y : r.ker) : r.ker) : G) = eval H σ f (n : G) := by
  obtain ⟨K, hK⟩ := f.property
  exact ⟨K.comap r.ker.subtype continuous_subtype_val, fun y n =>
    congrArg (fun F : EquivariantFunctions H σ => F.1 (n : G))
      (hK ⟨(y : r.ker), y.property⟩)⟩

/-- Restriction of an actual compact-induced function to the actual kernel.
The uniform right stabilizer is pulled back along the kernel inclusion. -/
def splitKernelCompactRestrict (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (f : CompactFunctions H σ) :
    CompactFunctions (H.comap r.ker.subtype)
      (σ.comp (r.ker.subtype.subgroupComap H)) :=
  compactFunctionOf (H.comap r.ker.subtype) (σ.comp (r.ker.subtype.subgroupComap H))
    (fun n : r.ker => eval H σ f.1 (n : G))
    (fun i n => f.1.1.property (r.ker.subtype.subgroupComap H i) (n : G))
    (Classical.choose (exists_openSubgroup_splitKernel_restrict r H σ f.1))
    (Classical.choose_spec (exists_openSubgroup_splitKernel_restrict r H σ f.1))
    (isCompact_quotientSupport_splitKernel_restrict r s hrs hr hs H hsH σ f)

/-- The extension of a compact-induced kernel function has compact actual
projected nonzero support in `H \ G`. -/
theorem isCompact_quotientSupport_splitKernelExtendFunction (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H) (σ : Representation R H V)
    (k : CompactFunctions (H.comap r.ker.subtype)
      (σ.comp (r.ker.subtype.subgroupComap H))) :
    IsCompact (quotientSupport H (splitKernelExtendFunction r s hrs H hsH σ k.1.1.1)) := by
  rw [quotientSupport_splitKernel_extend r s hrs hr hs H hsH σ]
  exact k.2.image (splitKernelLeftQuotientHomeomorph r s hrs hr hs H hsH).continuous

/-- The extension has a uniform open right stabilizer in `G`, derived from its
covariance, local constancy and compact projected support. -/
theorem exists_openSubgroup_splitKernelExtendFunction [LocallyCompactSpace G]
    (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (hσ : IsSmooth σ)
    (k : CompactFunctions (H.comap r.ker.subtype)
      (σ.comp (r.ker.subtype.subgroupComap H))) :
    ∃ K : OpenSubgroup G, ∀ (y : K) (x : G),
      splitKernelExtendFunction r s hrs H hsH σ k.1.1.1 (x * (y : G)) =
        splitKernelExtendFunction r s hrs H hsH σ k.1.1.1 x :=
  ⟨locallyConstantCompactOpenStabilizer H hH σ
      (splitKernelExtendFunction r s hrs H hsH σ k.1.1.1)
      (splitKernelExtendFunction_covariant r s hrs H hsH σ k.1.1.1 k.1.1.property)
      (splitKernelExtendFunction_isLocallyConstant r s hrs hr hs H hsH σ hσ k.1.1.1
        (eval_isLocallyConstant _ _ k.1))
      (isCompact_quotientSupport_splitKernelExtendFunction r s hrs hr hs H hsH σ k),
    fun y x => y.property x⟩

/-- Extend an actual compact-induced kernel function using the section action.
Local constancy and compact quotient support supply a uniform open stabilizer. -/
def splitKernelCompactExtend [LocallyCompactSpace G] (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (hσ : IsSmooth σ)
    (k : CompactFunctions (H.comap r.ker.subtype)
      (σ.comp (r.ker.subtype.subgroupComap H))) : CompactFunctions H σ :=
  compactFunctionOfLocallyConstant H hH σ
    (splitKernelExtendFunction r s hrs H hsH σ k.1.1.1)
    (splitKernelExtendFunction_covariant r s hrs H hsH σ k.1.1.1 k.1.1.property)
    (splitKernelExtendFunction_isLocallyConstant r s hrs hr hs H hsH σ hσ k.1.1.1
      (eval_isLocallyConstant _ _ k.1))
    (isCompact_quotientSupport_splitKernelExtendFunction r s hrs hr hs H hsH σ k)

/-- Restriction identifies compact induction, restricted to the kernel, with
compact induction from the actual intersection subgroup of the kernel. -/
def splitKernelCompactEquiv [LocallyCompactSpace G] (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (hσ : IsSmooth σ) :
    Representation.Equiv ((compactInduced H σ).comp r.ker.subtype)
      (compactInduced (H.comap r.ker.subtype) (σ.comp (r.ker.subtype.subgroupComap H))) where
  toLinearMap :=
    { toFun := splitKernelCompactRestrict r s hrs hr hs H hsH σ
      map_add' f g := by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext n
        rfl
      map_smul' c f := by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext n
        rfl }
  invFun := splitKernelCompactExtend r s hrs hr hs H hH hsH σ hσ
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact (splitKernel_apply_eq r s hrs H hsH σ f.1.1.1 f.1.1.property g).symm
  right_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext n
    exact splitKernelExtendFunction_coe r s hrs H hsH σ k.1.1.1 n
  isIntertwining' n := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    rfl

@[simp] theorem splitKernelCompactEquiv_eval [LocallyCompactSpace G]
    (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (hσ : IsSmooth σ)
    (f : CompactFunctions H σ) (n : r.ker) :
    eval (H.comap r.ker.subtype) (σ.comp (r.ker.subtype.subgroupComap H))
      (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ f).1 n =
        eval H σ f.1 (n : G) := rfl

@[simp] theorem splitKernelCompactEquiv_symm_eval [LocallyCompactSpace G]
    (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (hσ : IsSmooth σ)
    (k : CompactFunctions (H.comap r.ker.subtype)
      (σ.comp (r.ker.subtype.subgroupComap H))) (g : G) :
    eval H σ ((splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ).symm k).1 g =
      σ (splitKernelSection s H hsH (r g))
        (eval (H.comap r.ker.subtype) (σ.comp (r.ker.subtype.subgroupComap H))
          k.1 (splitKernelCoordinate r s hrs g)) := rfl

/-- The inverse formula with the actual split coordinates written out: the
section value `s (r g)` lifted into `H`, and `(s (r g))⁻¹ * g` lifted into the
actual kernel. -/
theorem splitKernelCompactEquiv_symm_eval_coordinates [LocallyCompactSpace G]
    (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (hσ : IsSmooth σ)
    (k : CompactFunctions (H.comap r.ker.subtype)
      (σ.comp (r.ker.subtype.subgroupComap H))) (g : G) :
    eval H σ ((splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ).symm k).1 g =
      σ ⟨s (r g), hsH (r g)⟩
        (eval (H.comap r.ker.subtype) (σ.comp (r.ker.subtype.subgroupComap H))
          k.1 ⟨(s (r g))⁻¹ * g,
            MonoidHom.mem_ker.mpr (map_splitKernelCoordinate r s hrs g)⟩) := rfl

/-- Left inverse law: extending the restriction recovers the function. -/
theorem splitKernelCompactEquiv_symm_apply_apply [LocallyCompactSpace G]
    (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (hσ : IsSmooth σ) (f : CompactFunctions H σ) :
    (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ).symm
      (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ f) = f :=
  (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ).symm_apply_apply f

/-- Right inverse law: restricting the extension recovers the kernel function. -/
theorem splitKernelCompactEquiv_apply_symm_apply [LocallyCompactSpace G]
    (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (hσ : IsSmooth σ)
    (k : CompactFunctions (H.comap r.ker.subtype)
      (σ.comp (r.ker.subtype.subgroupComap H))) :
    splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ
      ((splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ).symm k) = k :=
  (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ).apply_symm_apply k

/-- Kernel equivariance: restriction intertwines right translation by every
element of the actual kernel. -/
theorem splitKernelCompactEquiv_translate [LocallyCompactSpace G]
    (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
    (σ : Representation R H V) (hσ : IsSmooth σ)
    (n : r.ker) (f : CompactFunctions H σ) :
    splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ
        (compactInduced H σ (n : G) f) =
      compactInduced (H.comap r.ker.subtype) (σ.comp (r.ker.subtype.subgroupComap H)) n
        (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ f) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ).toIntertwiningMap n f

variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- Restrict a coefficient intertwiner to the actual kernel intersection. -/
def splitKernelInducingMap (r : G →* L) (H : Subgroup G)
    {σ : Representation R H V} {τ : Representation R H W}
    (T : σ.IntertwiningMap τ) :
    Representation.IntertwiningMap (σ.comp (r.ker.subtype.subgroupComap H))
      (τ.comp (r.ker.subtype.subgroupComap H)) where
  toLinearMap := T.toLinearMap
  isIntertwining' i := T.isIntertwining' (r.ker.subtype.subgroupComap H i)

/-- Kernel restriction commutes with every coefficient intertwiner in
independent coefficient universes. -/
theorem splitKernelCompactEquiv_natural [LocallyCompactSpace G]
    (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
    {σ : Representation R H V} {τ : Representation R H W}
    (hσ : IsSmooth σ) (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)
    (f : CompactFunctions H σ) :
    splitKernelCompactEquiv r s hrs hr hs H hH hsH τ hτ (compactInducedMap H T f) =
      compactInducedMap (H.comap r.ker.subtype) (splitKernelInducingMap r H T)
        (splitKernelCompactEquiv r s hrs hr hs H hH hsH σ hσ f) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext n
  rfl

end Langlands.Induction
