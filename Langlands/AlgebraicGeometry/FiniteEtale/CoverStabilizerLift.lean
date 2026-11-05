import Langlands.AlgebraicGeometry.FiniteEtale.CoverPointStabilizer

/-! # Lifting stabilizers of a selected lift to a cover fundamental group -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

section CompositeCovers

variable {S : Scheme.{u}} (Y : Cover S)

/-- A finite etale cover `Z → Y` of the total scheme of a cover `Y → S`, regarded
as the finite etale cover `Z → Y → S` of `S`. -/
def compCover (Z : Cover Y.obj.left) : Cover S :=
  cover (Z.obj.hom ≫ Y.obj.hom)

@[simp]
theorem compCover_obj_left (Z : Cover Y.obj.left) : (compCover Y Z).obj.left = Z.obj.left :=
  rfl

@[simp]
theorem compCover_obj_hom (Z : Cover Y.obj.left) :
    (compCover Y Z).obj.hom = Z.obj.hom ≫ Y.obj.hom :=
  rfl

/-- The structure morphism `Z → Y`, as a morphism of covers of `S`. -/
def compCoverProj (Z : Cover Y.obj.left) : compCover Y Z ⟶ Y :=
  ObjectProperty.homMk (Over.homMk Z.obj.hom rfl)

@[simp]
theorem compCoverProj_hom_left (Z : Cover Y.obj.left) :
    (compCoverProj Y Z).hom.left = Z.obj.hom :=
  rfl

/-- A morphism of covers of `Y`, as a morphism of the composite covers of `S`. -/
def compCoverMap {Z Z' : Cover Y.obj.left} (k : Z ⟶ Z') : compCover Y Z ⟶ compCover Y Z' :=
  ObjectProperty.homMk (Over.homMk k.hom.left (by
    change k.hom.left ≫ Z'.obj.hom ≫ Y.obj.hom = Z.obj.hom ≫ Y.obj.hom
    rw [← Category.assoc, Over.w k.hom]))

@[simp]
theorem compCoverMap_hom_left {Z Z' : Cover Y.obj.left} (k : Z ⟶ Z') :
    (compCoverMap Y k).hom.left = k.hom.left :=
  rfl

/-- For a cover `W` of `S`, the first projection `W ×_S Y → W` is a morphism of covers of `S`
from the composite of the pulled-back cover `W ×_S Y → Y` with `Y → S`. -/
def compCoverPullbackFst (W : Cover S) :
    compCover Y ((pullbackFunctor Y.obj.hom).obj W) ⟶ W :=
  ObjectProperty.homMk (Over.homMk (Limits.pullback.fst W.obj.hom Y.obj.hom)
    (by
      change Limits.pullback.fst W.obj.hom Y.obj.hom ≫ W.obj.hom =
        Limits.pullback.snd W.obj.hom Y.obj.hom ≫ Y.obj.hom
      exact Limits.pullback.condition))

@[simp]
theorem compCoverPullbackFst_hom_left (W : Cover S) :
    (compCoverPullbackFst Y W).hom.left = Limits.pullback.fst W.obj.hom Y.obj.hom :=
  rfl

end CompositeCovers

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))

section Fibers

variable {s} {Y : Cover S} (x : Fiber s Y)

/-- A lift of `x.left` to a cover `Z` of `Y` is a lift of `s` to the composite cover. -/
def compFiber (Z : Cover Y.obj.left) (z : Fiber x.left Z) : Fiber s (compCover Y Z) :=
  Over.homMk z.left (by
    change z.left ≫ Z.obj.hom ≫ Y.obj.hom = s
    rw [← Category.assoc, Over.w z]
    exact Over.w x)

@[simp]
theorem compFiber_left (Z : Cover Y.obj.left) (z : Fiber x.left Z) :
    (compFiber x Z z).left = z.left :=
  rfl

/-- The image of `compFiber` lies over `x`. -/
theorem compFiber_comp_proj (Z : Cover Y.obj.left) (z : Fiber x.left Z) :
    compFiber x Z z ≫ (compCoverProj Y Z).hom = x := by
  apply Over.OverMorphism.ext
  exact Over.w z

/-- `compFiber` is natural for morphisms of covers of `Y`. -/
theorem compFiber_comp {Z Z' : Cover Y.obj.left} (k : Z ⟶ Z') (z : Fiber x.left Z) :
    compFiber x Z' (z ≫ k.hom) = compFiber x Z z ≫ (compCoverMap Y k).hom :=
  rfl

/-- A lift of `s` to the composite cover that lies over `x` is a lift of `x.left` to `Z`. -/
def fiberOfCompFiber (Z : Cover Y.obj.left) (w : Fiber s (compCover Y Z))
    (hw : w ≫ (compCoverProj Y Z).hom = x) : Fiber x.left Z :=
  Over.homMk w.left (by
    have := congrArg CommaMorphism.left hw
    simpa using this)

@[simp]
theorem fiberOfCompFiber_left (Z : Cover Y.obj.left) (w : Fiber s (compCover Y Z))
    (hw : w ≫ (compCoverProj Y Z).hom = x) : (fiberOfCompFiber x Z w hw).left = w.left :=
  rfl

end Fibers

section Lift

variable {s} {hs} {Y : Cover S} {x : Fiber s Y}

/-- An element of the stabilizer of `x` preserves the lifts over `x` in the composite cover. -/
theorem smul_compFiber_comp_proj (g : FundamentalGroup s hs) (hg : g • x = x)
    (Z : Cover Y.obj.left) (z : Fiber x.left Z) :
    (g • compFiber x Z z) ≫ (compCoverProj Y Z).hom = x := by
  rw [← smul_naturality, compFiber_comp_proj, hg]

/-- The action of a stabilizer element of `x` on the lifts of `x.left` to a cover of `Y`. -/
def stabilizerLiftFun (g : FundamentalGroup s hs) (hg : g • x = x) (Z : Cover Y.obj.left)
    (z : Fiber x.left Z) : Fiber x.left Z :=
  fiberOfCompFiber x Z (g • compFiber x Z z) (smul_compFiber_comp_proj g hg Z z)

theorem compFiber_stabilizerLiftFun (g : FundamentalGroup s hs) (hg : g • x = x)
    (Z : Cover Y.obj.left) (z : Fiber x.left Z) :
    compFiber x Z (stabilizerLiftFun g hg Z z) = g • compFiber x Z z :=
  Over.OverMorphism.ext rfl

theorem stabilizerLiftFun_mul (g g' : FundamentalGroup s hs) (hg : g • x = x)
    (hg' : g' • x = x) (hgg' : (g * g') • x = x) (Z : Cover Y.obj.left) (z : Fiber x.left Z) :
    stabilizerLiftFun (g * g') hgg' Z z =
      stabilizerLiftFun g hg Z (stabilizerLiftFun g' hg' Z z) := by
  apply Over.OverMorphism.ext
  change ((g * g') • compFiber x Z z).left =
    (g • compFiber x Z (stabilizerLiftFun g' hg' Z z)).left
  rw [compFiber_stabilizerLiftFun, mul_smul]

theorem stabilizerLiftFun_one (h1 : (1 : FundamentalGroup s hs) • x = x)
    (Z : Cover Y.obj.left) (z : Fiber x.left Z) :
    stabilizerLiftFun 1 h1 Z z = z := by
  apply Over.OverMorphism.ext
  change ((1 : FundamentalGroup s hs) • compFiber x Z z).left = z.left
  rw [one_smul]
  rfl

/-- The stabilizer action on the lifts of `x.left` to `Z`, as a bijection. -/
def stabilizerLiftEquiv (g : FundamentalGroup s hs) (hg : g • x = x) (Z : Cover Y.obj.left) :
    Fiber x.left Z ≃ Fiber x.left Z where
  toFun := stabilizerLiftFun g hg Z
  invFun := stabilizerLiftFun g⁻¹ (inv_smul_eq_iff.mpr hg.symm) Z
  left_inv z := by
    apply Over.OverMorphism.ext
    change (g⁻¹ • compFiber x Z (stabilizerLiftFun g hg Z z)).left = z.left
    rw [compFiber_stabilizerLiftFun, inv_smul_smul]
    rfl
  right_inv z := by
    apply Over.OverMorphism.ext
    change (g • compFiber x Z (stabilizerLiftFun g⁻¹ _ Z z)).left = z.left
    rw [compFiber_stabilizerLiftFun, smul_inv_smul]
    rfl

/-- `stabilizerLiftFun` is natural for morphisms of covers of `Y`. -/
theorem stabilizerLiftFun_comp (g : FundamentalGroup s hs) (hg : g • x = x)
    {Z Z' : Cover Y.obj.left} (k : Z ⟶ Z') (z : Fiber x.left Z) :
    stabilizerLiftFun g hg Z' (z ≫ k.hom) = stabilizerLiftFun g hg Z z ≫ k.hom := by
  apply Over.OverMorphism.ext
  change (g • compFiber x Z' (z ≫ k.hom)).left = (g • compFiber x Z z).left ≫ k.hom.left
  rw [compFiber_comp, smul_naturality]
  rfl

variable (s hs Y x)

/-- **The lift of a stabilizer element.** For `g` in the fundamental group at `s` fixing the
selected lift `x`, the natural automorphism of the fibre functor at `x.left` acting on each
fibre `Fiber x.left Z` as `g` acts on the corresponding lifts over `x` in the composite cover
`Z → Y → S`. -/
def stabilizerLift (ht : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z))
    (g : FundamentalGroup s hs) (hg : g • x = x) : FundamentalGroup x.left ht :=
  NatIso.ofComponents
    (fun Z => ObjectProperty.isoMk _ (stabilizerLiftEquiv g hg Z).toIso)
    (by
      intro Z Z' k
      apply ObjectProperty.hom_ext
      ext z
      exact stabilizerLiftFun_comp g hg k z)

variable {s hs Y x}

@[simp]
theorem stabilizerLift_smul (ht : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z))
    (g : FundamentalGroup s hs) (hg : g • x = x) (Z : Cover Y.obj.left) (z : Fiber x.left Z) :
    stabilizerLift s hs Y x ht g hg • z = stabilizerLiftFun g hg Z z :=
  rfl

/-- The lift acts on the underlying morphisms exactly as `g` acts in the composite cover. -/
theorem stabilizerLift_smul_left (ht : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z))
    (g : FundamentalGroup s hs) (hg : g • x = x) (Z : Cover Y.obj.left) (z : Fiber x.left Z) :
    (stabilizerLift s hs Y x ht g hg • z).left = (g • compFiber x Z z).left :=
  rfl

end Lift

section Image

variable (Y : Cover S) (x : Fiber s Y) (ht : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z))

/-- **Lifting equation.** The induced homomorphism of fundamental groups sends the lift of a
stabilizer element `g` back to `g`. -/
theorem fundamentalGroupMap_stabilizerLift (g : FundamentalGroup s hs) (hg : g • x = x) :
    fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs (stabilizerLift s hs Y x ht g hg) =
      g := by
  apply fundamentalGroup_ext
  intro W w
  apply Over.OverMorphism.ext
  rw [fundamentalGroupMap_smul_left, stabilizerLift_smul_left]
  have hw : compFiber x _ (pullbackFiberEquiv Y.obj.hom x.left s (Over.w x) W w) ≫
      (compCoverPullbackFst Y W).hom = w := by
    apply Over.OverMorphism.ext
    exact pullbackFiberEquiv_apply_left_fst Y.obj.hom x.left s (Over.w x) W w
  conv_rhs => rw [← hw, smul_naturality]
  rfl

/-- The lifts of all stabilizer elements, as a group homomorphism on the stabilizer of `x`. -/
def stabilizerLiftHom :
    MulAction.stabilizer (FundamentalGroup s hs) x →* FundamentalGroup x.left ht where
  toFun g := stabilizerLift s hs Y x ht g g.2
  map_one' := by
    apply fundamentalGroup_ext
    intro Z z
    rw [one_smul]
    exact stabilizerLiftFun_one (one_smul _ x) Z z
  map_mul' g g' := by
    apply fundamentalGroup_ext
    intro Z z
    rw [mul_smul]
    exact stabilizerLiftFun_mul g.1 g'.1 g.2 g'.2 (g * g').2 Z z

@[simp]
theorem stabilizerLiftHom_apply (g : MulAction.stabilizer (FundamentalGroup s hs) x) :
    stabilizerLiftHom s hs Y x ht g = stabilizerLift s hs Y x ht g g.2 :=
  rfl

/-- The stabilizer lift is a section of the induced homomorphism over the stabilizer. -/
theorem fundamentalGroupMap_comp_stabilizerLiftHom :
    (fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs).comp
        (stabilizerLiftHom s hs Y x ht) =
      (MulAction.stabilizer (FundamentalGroup s hs) x).subtype := by
  ext g : 1
  exact fundamentalGroupMap_stabilizerLift s hs Y x ht g g.2

/-- **Image of a cover fundamental group.** An element of the fundamental group at `s` lies in
the image of the fundamental group of the cover `Y` at the selected lift `x` if and only if it
fixes `x`. -/
theorem exists_fundamentalGroupMap_eq_iff (g : FundamentalGroup s hs) :
    (∃ σ : FundamentalGroup x.left ht,
      fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs σ = g) ↔ g • x = x := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact fundamentalGroupMap_fixes_lift s hs Y x ht σ
  · intro hg
    exact ⟨stabilizerLift s hs Y x ht g hg, fundamentalGroupMap_stabilizerLift s hs Y x ht g hg⟩

/-- The image of the induced homomorphism is the stabilizer of the selected lift. -/
theorem range_fundamentalGroupMap :
    (fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs).range =
      MulAction.stabilizer (FundamentalGroup s hs) x := by
  ext g
  exact (exists_fundamentalGroupMap_eq_iff s hs Y x ht g).trans MulAction.mem_stabilizer_iff.symm

end Image

end Langlands.AlgebraicGeometry.FiniteEtale
