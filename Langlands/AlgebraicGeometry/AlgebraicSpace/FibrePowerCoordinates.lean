import Langlands.AlgebraicGeometry.AlgebraicSpace.ChartFibrePower

/-! # Coordinates of points of fibre powers -/

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Left cancellation of the spectrum of a homomorphism of fields. -/
theorem Spec_map_field_cancel {K L : Type u} [Field K] [Field L] (φ : K →+* L) {X : Scheme.{u}}
    {g h : Spec (CommRingCat.of K) ⟶ X}
    (e : Spec.map (CommRingCat.ofHom φ) ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ h) : g = h := by
  obtain ⟨⟨x, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g
  obtain ⟨⟨y, β⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective h
  simp only [Scheme.SpecToEquivOfField_symm_apply] at e ⊢
  let s0 : Spec (CommRingCat.of L) := IsLocalRing.closedPoint L
  have hpt : ∀ (z : X) (γ : X.residueField z ⟶ CommRingCat.of K),
      (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map γ ≫ X.fromSpecResidueField z) s0 = z := by
    intro z γ
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hxy : x = y := by rw [← hpt x α, e, hpt y β]
  subst hxy
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at e
  have e' := (cancel_mono (X.fromSpecResidueField x)).mp e
  have e'' := Spec.map_injective e'
  have : α = β := by
    ext a
    exact φ.injective (congrArg (fun f => f.hom a) e'')
  rw [this]

namespace ChartFibrePower

variable {S : Scheme.{u}} {X : Presheaf S} {V : Over S} {a : (schemeYoneda S).obj V ⟶ X}
  {ι : Type v} {κ : Type w}

/-- The `i`-th coordinate of a point `p` of a fibre power: the composite of the canonical
morphism `Spec κ(p) ⟶ P` with the `i`-th projection. -/
def coord (P : ChartFibrePower a ι) (p : P.obj.left) (i : ι) :
    Spec (P.obj.left.residueField p) ⟶ V.left :=
  P.obj.left.fromSpecResidueField p ≫ (P.pr i).left

/-- A point of a fibre power is distinct when its coordinates are pairwise different. -/
def IsDistinct (P : ChartFibrePower a ι) (p : P.obj.left) : Prop :=
  Function.Injective (P.coord p)

/-- The morphism between fibre powers induced by a map of index types. -/
def mapIndex (P : ChartFibrePower a ι) (Q : ChartFibrePower a κ) (e : κ → ι) :
    P.obj ⟶ Q.obj :=
  Q.lift (fun k => P.pr (e k)) (fun k l => P.w (e k) (e l))

@[reassoc (attr := simp)]
theorem mapIndex_pr (P : ChartFibrePower a ι) (Q : ChartFibrePower a κ) (e : κ → ι) (k : κ) :
    P.mapIndex Q e ≫ Q.pr k = P.pr (e k) :=
  Q.lift_pr _ _ k

theorem coord_mapIndex (P : ChartFibrePower a ι) (Q : ChartFibrePower a κ) (e : κ → ι)
    (p : P.obj.left) (k : κ) :
    Spec.map ((P.mapIndex Q e).left.residueFieldMap p) ≫ Q.coord ((P.mapIndex Q e).left p) k =
      P.coord p (e k) := by
  rw [coord, ← Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    Category.assoc, ← Over.comp_left, mapIndex_pr]
  rfl

theorem coord_mapIndex_eq_iff (P : ChartFibrePower a ι) (Q : ChartFibrePower a κ) (e : κ → ι)
    (p : P.obj.left) (k l : κ) :
    Q.coord ((P.mapIndex Q e).left p) k = Q.coord ((P.mapIndex Q e).left p) l ↔
      P.coord p (e k) = P.coord p (e l) := by
  rw [← coord_mapIndex P Q e p k, ← coord_mapIndex P Q e p l]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Spec_map_field_cancel _ h

/-- The permutation action on a fibre power. -/
def perm (P : ChartFibrePower a ι) (σ : Equiv.Perm ι) : P.obj ⟶ P.obj :=
  P.mapIndex P σ

@[reassoc (attr := simp)]
theorem perm_pr (P : ChartFibrePower a ι) (σ : Equiv.Perm ι) (i : ι) :
    P.perm σ ≫ P.pr i = P.pr (σ i) :=
  P.mapIndex_pr P σ i

theorem perm_one (P : ChartFibrePower a ι) : P.perm 1 = 𝟙 P.obj :=
  P.hom_ext _ _ fun i => by simp

theorem perm_mul (P : ChartFibrePower a ι) (σ τ : Equiv.Perm ι) :
    P.perm σ ≫ P.perm τ = P.perm (σ * τ) :=
  P.hom_ext _ _ fun i => by simp

/-- The test scheme `Spec κ(p)` over `S` of a point of a fibre power. -/
def pointTest (P : ChartFibrePower a ι) (p : P.obj.left) : Over S :=
  Over.mk (P.obj.left.fromSpecResidueField p ≫ P.obj.hom)

/-- The canonical morphism from the test scheme of a point. -/
def pointHom (P : ChartFibrePower a ι) (p : P.obj.left) : P.pointTest p ⟶ P.obj :=
  Over.homMk (P.obj.left.fromSpecResidueField p)

theorem pointHom_pr_left (P : ChartFibrePower a ι) (p : P.obj.left) (i : ι) :
    (P.pointHom p ≫ P.pr i).left = P.coord p i :=
  rfl

/-- A point whose coordinates are the coordinates of a map of index types applied to another
point lies in the range of the induced morphism. -/
theorem mem_range_mapIndex (P : ChartFibrePower a ι) (Q : ChartFibrePower a κ) (e : κ → ι)
    (f : ι → κ) (q : Q.obj.left) (h : ∀ k, Q.coord q (f (e k)) = Q.coord q k) :
    q ∈ Set.range (Q.mapIndex P f ≫ P.mapIndex Q e).left := by
  have key : Q.pointHom q ≫ Q.mapIndex P f ≫ P.mapIndex Q e = Q.pointHom q := by
    refine Q.hom_ext _ _ fun k => ?_
    apply Over.OverMorphism.ext
    simp only [Category.assoc, mapIndex_pr]
    exact h k
  have key' : Q.obj.left.fromSpecResidueField q ≫ (Q.mapIndex P f).left ≫
      (P.mapIndex Q e).left = Q.obj.left.fromSpecResidueField q := by
    have h := congrArg Over.Hom.left key
    rw [Over.comp_left, Over.comp_left] at h
    exact h
  refine ⟨q, ?_⟩
  let s0 : Spec (Q.obj.left.residueField q) := IsLocalRing.closedPoint _
  have h2 := congrArg (fun g => g s0) key'
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at h2
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  exact h2

end ChartFibrePower

/-- Pigeonhole: if `x` and `y` are injective families of `n` elements and no extension of `x`
by an entry of `y` is injective, then `y` is a permutation of `x`. -/
theorem exists_perm_of_not_injective_snoc {T : Type*} {n : ℕ} (x y : Fin n → T)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (h : ∀ b, ¬ Function.Injective (Fin.snoc x (y b) : Fin (n + 1) → T)) :
    ∃ π : Equiv.Perm (Fin n), ∀ b, y b = x (π b) := by
  have hex : ∀ b, ∃ i, y b = x i := by
    intro b
    by_contra hne
    push Not at hne
    apply h b
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd hij (hne j)
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd hij.symm (hne i)
      | cast j =>
        simp only [Fin.snoc_castSucc] at hij
        rw [hx hij]
  choose π0 hπ0 using hex
  have hinj : Function.Injective π0 := fun b c hbc => hy (by rw [hπ0 b, hπ0 c, hbc])
  exact ⟨Equiv.ofBijective π0 (Finite.injective_iff_bijective.mp hinj), hπ0⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
