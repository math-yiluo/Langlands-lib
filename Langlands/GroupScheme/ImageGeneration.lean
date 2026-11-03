import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Reductive.Basic

/-! # The closed subgroup envelope of an actual scheme morphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}} {G : GroupScheme B} {V : Over B}

/-- Containment of the image on every test scheme over the base. -/
def SubgroupFunctor.ContainsImage (F : SubgroupFunctor G) (f : V ⟶ G.X) : Prop :=
  ∀ (T : Over B) (v : T ⟶ V), v ≫ f ∈ F.carrier T

theorem SubgroupFunctor.containsImage_iff (F : SubgroupFunctor G) (f : V ⟶ G.X) :
    F.ContainsImage f ↔ f ∈ F.carrier V := by
  constructor
  · intro h
    simpa using h V (𝟙 V)
  · intro h T v
    exact F.comp_mem v h

/-- Factorization of an actual scheme morphism through a group-scheme homomorphism. -/
def FactorsThrough {H : GroupScheme B} (f : V ⟶ G.X) (i : H ⟶ G) : Prop :=
  ∃ g : V ⟶ H.X, g ≫ i.hom.hom = f

theorem factorsThrough_iff_containsImage {H : GroupScheme B} (f : V ⟶ G.X)
    (i : H ⟶ G) :
    FactorsThrough f i ↔ (SubgroupFunctor.range i).ContainsImage f := by
  rw [SubgroupFunctor.containsImage_iff]
  rfl

/-- Intersection of all represented closed subgroup functors through which `f`
factors as a morphism. Representability of this intersection is not assumed. -/
def closedImageEnvelope (f : V ⟶ G.X) : SubgroupFunctor G where
  carrier T :=
    { carrier := {x | ∀ (H : GroupScheme B) (i : H ⟶ G),
        IsClosedSubgroup i → FactorsThrough f i → x ∈ (SubgroupFunctor.range i).carrier T}
      one_mem' := fun _ i _ _ => (SubgroupFunctor.range i).carrier T |>.one_mem
      mul_mem' := fun hx hy H i hi hf =>
        ((SubgroupFunctor.range i).carrier T).mul_mem (hx H i hi hf) (hy H i hi hf)
      inv_mem' := fun hx H i hi hf =>
        ((SubgroupFunctor.range i).carrier T).inv_mem (hx H i hi hf) }
  comp_mem a x hx H i hi hf := (SubgroupFunctor.range i).comp_mem a (hx H i hi hf)

/-- The universal point of the source, and consequently its points on all tests,
belongs to the closed envelope. -/
theorem closedImageEnvelope_containsImage (f : V ⟶ G.X) :
    (closedImageEnvelope f).ContainsImage f := by
  intro T v H i _ hf
  obtain ⟨g, rfl⟩ := hf
  exact SubgroupFunctor.mem_range.2 ⟨v ≫ g, Category.assoc _ _ _⟩

/-- Minimality among all actual closed subgroup inclusions admitting a factorization. -/
theorem closedImageEnvelope_le (f : V ⟶ G.X) {H : GroupScheme B} (i : H ⟶ G)
    (hi : IsClosedSubgroup i) (hf : FactorsThrough f i) :
    closedImageEnvelope f ≤ SubgroupFunctor.range i :=
  fun _ _ hx => hx H i hi hf

/-- A closed subgroup functor containing the image contains the envelope. -/
theorem closedImageEnvelope_le_of_containsImage (f : V ⟶ G.X)
    {F : SubgroupFunctor G} {H : GroupScheme B} (i : H ⟶ G)
    (hF : F.IsRepresentedBy i) (hi : IsClosedSubgroup i) (hf : F.ContainsImage f) :
    closedImageEnvelope f ≤ F := by
  rw [← hF.2] at hf ⊢
  exact closedImageEnvelope_le f i hi ((factorsThrough_iff_containsImage f i).2 hf)

/-- An actual representative of the closed envelope. No geometric regularity
property or existence theorem is built into this data. -/
structure GeneratedImage (f : V ⟶ G.X) where
  group : GroupScheme B
  inclusion : group ⟶ G
  closed : IsClosedSubgroup inclusion
  represents : (closedImageEnvelope f).IsRepresentedBy inclusion

namespace GeneratedImage

variable {f : V ⟶ G.X} (D : GeneratedImage f)

/-- The actual source morphism into the representing subgroup. -/
def factor : V ⟶ D.group.X :=
  Classical.choose (SubgroupFunctor.mem_range.1 (by
    rw [D.represents.2]
    exact (SubgroupFunctor.containsImage_iff _ f).1 (closedImageEnvelope_containsImage f)))

theorem factor_comp : D.factor ≫ D.inclusion.hom.hom = f :=
  Classical.choose_spec (SubgroupFunctor.mem_range.1 (by
    rw [D.represents.2]
    exact (SubgroupFunctor.containsImage_iff _ f).1 (closedImageEnvelope_containsImage f)))

/-- The factorization holds on every scheme, including nonreduced tests. -/
theorem factor_comp_points {T : Over B} (v : T ⟶ V) :
    (v ≫ D.factor) ≫ D.inclusion.hom.hom = v ≫ f := by
  rw [Category.assoc, D.factor_comp]

theorem factor_unique (g : V ⟶ D.group.X) (hg : g ≫ D.inclusion.hom.hom = f) :
    g = D.factor := by
  letI : Mono D.inclusion.hom.hom := D.represents.1
  exact (cancel_mono D.inclusion.hom.hom).1 (hg.trans D.factor_comp.symm)

theorem range_le {K : GroupScheme B} (j : K ⟶ G) (hj : IsClosedSubgroup j)
    (hf : FactorsThrough f j) : SubgroupFunctor.range D.inclusion ≤ SubgroupFunctor.range j := by
  rw [D.represents.2]
  exact closedImageEnvelope_le f j hj hf

private theorem range_represents {K : GroupScheme B} (j : K ⟶ G)
    (hj : IsClosedSubgroup j) : (SubgroupFunctor.range j).IsRepresentedBy j := by
  letI : IsClosedImmersion j.hom.hom.left := hj
  exact ⟨Over.mono_of_mono_left _, rfl⟩

private def inclusionOnPoints {K : GroupScheme B} (j : K ⟶ G)
    (hj : IsClosedSubgroup j) (hf : FactorsThrough f j) (T : Over B) :
    (closedImageEnvelope f).carrier T →* (SubgroupFunctor.range j).carrier T where
  toFun x := ⟨x.val, closedImageEnvelope_le f j hj hf T x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Universal minimality as an actual homomorphism into every competing closed
subgroup; its inclusion into `G` is the given inclusion of the envelope. -/
def minimalHom {K : GroupScheme B} (j : K ⟶ G) (hj : IsClosedSubgroup j)
    (hf : FactorsThrough f j) : D.group ⟶ K :=
  D.represents.lift (range_represents j hj) (inclusionOnPoints j hj hf) (fun _ _ => rfl)

theorem minimalHom_comp {K : GroupScheme B} (j : K ⟶ G) (hj : IsClosedSubgroup j)
    (hf : FactorsThrough f j) : D.minimalHom j hj hf ≫ j = D.inclusion :=
  D.represents.lift_comp_eq (range_represents j hj)
    (inclusionOnPoints j hj hf) (fun _ _ => rfl) (fun _ _ => rfl)

theorem minimalHom_unique {K : GroupScheme B} (j : K ⟶ G) (hj : IsClosedSubgroup j)
    (hf : FactorsThrough f j) (a : D.group ⟶ K) (ha : a ≫ j = D.inclusion) :
    a = D.minimalHom j hj hf :=
  (range_represents j hj).hom_ext (ha.trans (D.minimalHom_comp j hj hf).symm)

/-- Two representatives of the envelope are uniquely isomorphic over the ambient group. -/
def iso (D' : GeneratedImage f) : D.group ≅ D'.group :=
  D.represents.isoOfIsRepresentedBy D'.represents

theorem iso_hom_comp (D' : GeneratedImage f) : (D.iso D').hom ≫ D'.inclusion = D.inclusion :=
  D.represents.isoOfIsRepresentedBy_hom_comp D'.represents

end GeneratedImage

end Langlands.GroupScheme
