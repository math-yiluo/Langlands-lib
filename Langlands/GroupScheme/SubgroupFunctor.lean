import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.KernelBaseChange

/-! # Subgroup functors of group schemes over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- A subgroup functor of a group scheme `G` over `S`: for every scheme `T` over `S`, a subgroup
of the `T`-valued points of `G`, stable under restriction along every morphism of test schemes. -/
structure SubgroupFunctor (G : GroupScheme S) where
  /-- The subgroup of `T`-valued points. -/
  carrier : ∀ T : Over S, Subgroup (T ⟶ G.X)
  /-- Restriction along a morphism of test schemes preserves membership. -/
  comp_mem : ∀ {T T' : Over S} (a : T' ⟶ T) {x : T ⟶ G.X}, x ∈ carrier T → a ≫ x ∈ carrier T'

namespace SubgroupFunctor

variable {G H : GroupScheme S}

/-- Subgroup functors with the same subgroups of points on every test scheme are equal. -/
@[ext] theorem ext {F F' : SubgroupFunctor G} (h : ∀ T, F.carrier T = F'.carrier T) :
    F = F' := by
  cases F
  cases F'
  congr
  funext T
  exact h T

/-- Pointwise inclusion of subgroups on every test scheme. -/
instance : PartialOrder (SubgroupFunctor G) :=
  PartialOrder.lift (fun F => F.carrier) fun _ _ h => ext (congrFun h)

theorem le_def {F F' : SubgroupFunctor G} : F ≤ F' ↔ ∀ T, F.carrier T ≤ F'.carrier T :=
  Iff.rfl

/-- The pointwise intersection of two subgroup functors. -/
instance : Min (SubgroupFunctor G) where
  min F F' :=
    { carrier := fun T => F.carrier T ⊓ F'.carrier T
      comp_mem := fun a _ hx => ⟨F.comp_mem a hx.1, F'.comp_mem a hx.2⟩ }

@[simp] theorem inf_carrier (F F' : SubgroupFunctor G) (T : Over S) :
    (F ⊓ F').carrier T = F.carrier T ⊓ F'.carrier T :=
  rfl

/-- The subgroup functor of all points. -/
instance : Top (SubgroupFunctor G) where
  top := { carrier := fun _ => ⊤, comp_mem := fun _ _ _ => Subgroup.mem_top _ }

/-- The subgroup functor of identity points. -/
instance : Bot (SubgroupFunctor G) where
  bot :=
    { carrier := fun _ => ⊥
      comp_mem := fun a x hx => by
        rw [Subgroup.mem_bot] at hx ⊢
        rw [hx]
        exact MonObj.comp_one a }

@[simp] theorem top_carrier (T : Over S) : (⊤ : SubgroupFunctor G).carrier T = ⊤ := rfl

@[simp] theorem bot_carrier (T : Over S) : (⊥ : SubgroupFunctor G).carrier T = ⊥ := rfl

/-- The points of `G` that factor through a group-scheme homomorphism `f : H ⟶ G`. -/
def range (f : H ⟶ G) : SubgroupFunctor G where
  carrier T := ((yonedaGrp.map f).app (op T)).hom.range
  comp_mem a x := by
    rintro ⟨y, rfl⟩
    exact ⟨a ≫ y, (Category.assoc a y f.hom.hom).symm⟩

theorem mem_range {f : H ⟶ G} {T : Over S} {x : T ⟶ G.X} :
    x ∈ (range f).carrier T ↔ ∃ y : T ⟶ H.X, y ≫ f.hom.hom = x :=
  Iff.rfl

/-- A homomorphism `f : H ⟶ G` represents `F` if it is a monomorphism of schemes over `S` and its
points are exactly the subgroups of `F`. Closedness of the immersion is a separate property. -/
def IsRepresentedBy (F : SubgroupFunctor G) (f : H ⟶ G) : Prop :=
  Mono f.hom.hom ∧ range f = F

/-- `F` is normalized by `F'`: conjugation by points of `F'` preserves points of `F`. -/
def IsNormalizedBy (F F' : SubgroupFunctor G) : Prop :=
  ∀ (T : Over S) (g x : T ⟶ G.X), g ∈ F'.carrier T → x ∈ F.carrier T → g * x * g⁻¹ ∈ F.carrier T

/-- A normal subgroup functor: its points are normal subgroups on every test scheme. -/
def IsNormal (F : SubgroupFunctor G) : Prop :=
  F.IsNormalizedBy ⊤

section BaseChange

variable {S' : Scheme.{u}} (b : S' ⟶ S)

/-- Base change of a subgroup functor: a point of the base change of `G` over `T'` belongs to it
when the corresponding point of `G`, on `T'` regarded over `S`, belongs to `F`. -/
def baseChange (F : SubgroupFunctor G) : SubgroupFunctor ((GroupScheme.baseChange b).obj G) where
  carrier T' := (F.carrier ((Over.map b).obj T')).comap (baseChangePointsEquiv b G T').toMonoidHom
  comp_mem a x hx := by
    change baseChangePointsEquiv b G _ (a ≫ x) ∈ F.carrier _
    rw [baseChangePointsEquiv_naturality]
    exact F.comp_mem _ hx

theorem mem_baseChange {F : SubgroupFunctor G} {T' : Over S'}
    {x : T' ⟶ ((GroupScheme.baseChange b).obj G).X} :
    x ∈ (F.baseChange b).carrier T' ↔
      baseChangePointsEquiv b G T' x ∈ F.carrier ((Over.map b).obj T') :=
  Iff.rfl

end BaseChange

end SubgroupFunctor

end Langlands.GroupScheme
