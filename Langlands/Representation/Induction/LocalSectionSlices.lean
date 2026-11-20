import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Smooth.SeparatingIntertwiners

/-! Restriction of covariant sections along a local group and an away argument. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Induction

open _root_.Representation

universe uG uA uH uV uW

variable {G : Type uG} [Group G]
  {A : Type uA} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {P : Subgroup G} {L : Subgroup H}
  {ρ : Representation ℂ P V} {σ : Representation ℂ L W}
  (α : A →* G) (j : H →ₜ* A) (jP : L →* P)
  (hjP : ∀ p : L, (jP p : G) = α (j p))
  (a : G) (ha : ∀ h : H, Commute a (α (j h)))
  (q : IntertwiningMap (ρ.comp jP) σ)

local instance : AddCommGroup (EquivariantFunctions P ρ) := Submodule.addCommGroup _

local instance : AddCommGroup (smoothVectors ((equivariantAction P ρ).comp α)) :=
  Submodule.addCommGroup _

include ha in
omit [IsTopologicalGroup A] [IsTopologicalGroup H] in
private theorem sliceArgument_mul (x k : H) :
    α (j (x * k)) * a = (α (j x) * a) * α (j k) := by
  rw [map_mul j, map_mul α, mul_assoc, ← (ha k).eq, ← mul_assoc]

include hjP ha in
private def sliceSection (f : smoothVectors ((equivariantAction P ρ).comp α)) :
    SmoothFunctions L σ :=
  ⟨⟨fun x => q (f.val.val (α (j x) * a)), by
      intro p x
      change q (f.val.val (α (j ((p : H) * x)) * a)) = σ p (q (f.val.val (α (j x) * a)))
      rw [map_mul j, map_mul α, mul_assoc, ← hjP p]
      exact (congrArg q (f.val.property (jP p) (α (j x) * a))).trans
        (IntertwiningMap.isIntertwining (ρ.comp jP) σ q p _)⟩, by
    obtain ⟨K, hK⟩ := f.property
    refine ⟨K.comap j.toMonoidHom j.continuous, ?_⟩
    intro k
    apply Subtype.ext
    funext x
    change q (f.val.val (α (j (x * (k : H))) * a)) = q (f.val.val (α (j x) * a))
    rw [sliceArgument_mul α j a ha]
    have h := hK ⟨j (k : H), k.property⟩
    exact congrArg (fun s : EquivariantFunctions P ρ => q (s.val (α (j x) * a))) h⟩

/-- Slice a section along `x ↦ α (j x) * a` and apply the coefficient intertwiner.
The away argument `a` centralizes `α (j H)`, so the slice intertwines right translation. -/
def localSliceIntertwiner :
    IntertwiningMap ((smoothPart ((equivariantAction P ρ).comp α)).comp j.toMonoidHom)
      (smoothInduced L σ) where
  toLinearMap :=
    { toFun := sliceSection α j jP hjP a ha q
      map_add' := by
        intro f f'
        apply Subtype.ext
        apply Subtype.ext
        funext x
        exact q.map_add' _ _
      map_smul' := by
        intro z f
        apply Subtype.ext
        apply Subtype.ext
        funext x
        exact q.map_smul' z _ }
  isIntertwining' k := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change q (f.val.val ((α (j x) * a) * α (j k))) = q (f.val.val (α (j (x * k)) * a))
    rw [sliceArgument_mul α j a ha]

@[simp] theorem eval_localSliceIntertwiner
    (f : smoothVectors ((equivariantAction P ρ).comp α)) (x : H) :
    eval L σ (localSliceIntertwiner α j jP hjP a ha q f) x =
      q (f.val.val (α (j x) * a)) := rfl

omit a ha q in
include hjP in
/-- If every ambient argument is local times away, separating coefficient maps
produce separating intertwiners from the restricted induced representation. -/
theorem hasSeparatingIntertwiners_localSlices
    (hcover : ∀ g : G, ∃ x : H, ∃ a : G, (∀ k : H, Commute a (α (j k))) ∧
      g = α (j x) * a)
    (hsep : HasSeparatingIntertwiners (ρ.comp jP) σ) :
    HasSeparatingIntertwiners
      ((smoothPart ((equivariantAction P ρ).comp α)).comp j.toMonoidHom) (smoothInduced L σ) := by
  intro f hf
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change f.val.val g = 0
  obtain ⟨x, a, ha, rfl⟩ := hcover g
  refine hsep (f.val.val (α (j x) * a)) fun q => ?_
  exact congrArg (fun s : SmoothFunctions L σ => eval L σ s x)
    (hf (localSliceIntertwiner α j jP hjP a ha q))

end Langlands.Induction
