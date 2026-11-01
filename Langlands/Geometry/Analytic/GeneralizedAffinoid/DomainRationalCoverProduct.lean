import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalNeighborhoodCover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan

/-! # Products of actual finite covers with supplied rational covers -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {U : Domain K A}

/-- Pairwise actual rational quotients give a common refinement of a finite
full-domain cover and a supplied ambient rational cover. -/
def rationalProduct (c : FiniteCover U) (r : FiniteRationalCover U) :
    FiniteCover U :=
  ofFintype
    (fun ij : Fin c.size × Fin r.size => (c.obj ij.1).rationalInter (r.chart ij.2))
    (fun ij => (c.obj ij.1).rationalInterLeft (r.chart ij.2) ≫ c.map ij.1)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := c.covers x hx
      obtain ⟨j, hj⟩ := r.covers x hx
      exact ⟨(i, j), hi, hj⟩)

@[simp] theorem rationalProduct_size (c : FiniteCover U) (r : FiniteRationalCover U) :
    (c.rationalProduct r).size = c.size * r.size := by
  simp [rationalProduct, ofFintype, Fintype.card_prod]

/-- Decode a component into its two original chosen indices. -/
def rationalProductIndexEquiv (c : FiniteCover U) (r : FiniteRationalCover U) :
    Fin (c.rationalProduct r).size ≃ Fin c.size × Fin r.size :=
  (Fintype.equivFin (Fin c.size × Fin r.size)).symm

/-- The component corresponding to a specified pair of original indices. -/
def rationalProductIndex (c : FiniteCover U) (r : FiniteRationalCover U)
    (i : Fin c.size) (j : Fin r.size) : Fin (c.rationalProduct r).size :=
  (c.rationalProductIndexEquiv r).symm (i, j)

@[simp] theorem rationalProductIndexEquiv_index (c : FiniteCover U)
    (r : FiniteRationalCover U) (i : Fin c.size) (j : Fin r.size) :
    c.rationalProductIndexEquiv r (c.rationalProductIndex r i j) = (i, j) :=
  (c.rationalProductIndexEquiv r).apply_symm_apply (i, j)

@[simp] theorem rationalProduct_obj (c : FiniteCover U) (r : FiniteRationalCover U)
    (k : Fin (c.rationalProduct r).size) :
    (c.rationalProduct r).obj k =
      (c.obj (c.rationalProductIndexEquiv r k).1).rationalInter
        (r.chart (c.rationalProductIndexEquiv r k).2) := rfl

/-- Each component retains the actual rational quotient over the original
full-domain component algebra. -/
@[simp] theorem rationalProduct_obj_algebra (c : FiniteCover U)
    (r : FiniteRationalCover U) (k : Fin (c.rationalProduct r).size) :
    ((c.rationalProduct r).obj k).algebra =
      (RationalChart.pullback (c.obj (c.rationalProductIndexEquiv r k).1).baseMap
        (r.chart (c.rationalProductIndexEquiv r k).2)).algebra := rfl

@[simp] theorem rationalProduct_obj_locus (c : FiniteCover U)
    (r : FiniteRationalCover U) (k : Fin (c.rationalProduct r).size) :
    ((c.rationalProduct r).obj k).locus =
      (c.obj (c.rationalProductIndexEquiv r k).1).locus ∩
        (r.chart (c.rationalProductIndexEquiv r k).2).locus := rfl

@[simp] theorem rationalProduct_obj_index (c : FiniteCover U)
    (r : FiniteRationalCover U) (i : Fin c.size) (j : Fin r.size) :
    (c.rationalProduct r).obj (c.rationalProductIndex r i j) =
      (c.obj i).rationalInter (r.chart j) := by
  rw [rationalProduct_obj, rationalProductIndexEquiv_index]

/-- The first projection uses each actual pulled quotient's bounded base map. -/
def rationalProductFst (c : FiniteCover U) (r : FiniteRationalCover U) :
    c.rationalProduct r ⟶ c where
  index k := (c.rationalProductIndexEquiv r k).1
  map k := (c.obj (c.rationalProductIndexEquiv r k).1).rationalInterLeft
    (r.chart (c.rationalProductIndexEquiv r k).2)

/-- The second projection uses the actual rational quotient transport. -/
def rationalProductSnd (c : FiniteCover U) (r : FiniteRationalCover U) :
    c.rationalProduct r ⟶ r.toFiniteCover where
  index k := (c.rationalProductIndexEquiv r k).2
  map k := (c.obj (c.rationalProductIndexEquiv r k).1).rationalInterRight
    (r.chart (c.rationalProductIndexEquiv r k).2)

@[simp] theorem rationalProductFst_index (c : FiniteCover U)
    (r : FiniteRationalCover U) (k : Fin (c.rationalProduct r).size) :
    (c.rationalProductFst r).index k = (c.rationalProductIndexEquiv r k).1 := rfl

@[simp] theorem rationalProductSnd_index (c : FiniteCover U)
    (r : FiniteRationalCover U) (k : Fin (c.rationalProduct r).size) :
    (c.rationalProductSnd r).index k = (c.rationalProductIndexEquiv r k).2 := rfl

/-- Pair the chosen indices and construct each actual bounded component
restriction by the full-test intersection lift. -/
def rationalProductLift {b c : FiniteCover U} {r : FiniteRationalCover U}
    (f : b ⟶ c) (g : b ⟶ r.toFiniteCover) : b ⟶ c.rationalProduct r where
  index i := c.rationalProductIndex r (f.index i) (g.index i)
  map i := rationalInterLift (f.map i) (g.map i) ≫
    eqToHom (c.rationalProduct_obj_index r (f.index i) (g.index i)).symm

@[simp] theorem rationalProductLift_index {b c : FiniteCover U}
    {r : FiniteRationalCover U} (f : b ⟶ c) (g : b ⟶ r.toFiniteCover)
    (i : Fin b.size) :
    (rationalProductLift f g).index i =
      c.rationalProductIndex r (f.index i) (g.index i) := rfl

@[simp] theorem rationalProductLift_fst {b c : FiniteCover U}
    {r : FiniteRationalCover U} (f : b ⟶ c) (g : b ⟶ r.toFiniteCover) :
    rationalProductLift f g ≫ c.rationalProductFst r = f := by
  apply Refinement.ext
  funext i
  change (c.rationalProductIndexEquiv r
    (c.rationalProductIndex r (f.index i) (g.index i))).1 = f.index i
  exact congrArg Prod.fst
    (c.rationalProductIndexEquiv_index r (f.index i) (g.index i))

@[simp] theorem rationalProductLift_snd {b c : FiniteCover U}
    {r : FiniteRationalCover U} (f : b ⟶ c) (g : b ⟶ r.toFiniteCover) :
    rationalProductLift f g ≫ c.rationalProductSnd r = g := by
  apply Refinement.ext
  funext i
  change (c.rationalProductIndexEquiv r
    (c.rationalProductIndex r (f.index i) (g.index i))).2 = g.index i
  exact congrArg Prod.snd
    (c.rationalProductIndexEquiv_index r (f.index i) (g.index i))

/-- Both chosen projection indices determine the pair index; uniqueness of
actual domain restrictions then determines the entire refinement. -/
theorem rationalProduct_hom_ext {b c : FiniteCover U} {r : FiniteRationalCover U}
    {f g : b ⟶ c.rationalProduct r}
    (hfst : f ≫ c.rationalProductFst r = g ≫ c.rationalProductFst r)
    (hsnd : f ≫ c.rationalProductSnd r = g ≫ c.rationalProductSnd r) : f = g := by
  apply Refinement.ext
  funext i
  apply (c.rationalProductIndexEquiv r).injective
  apply Prod.ext
  · exact congrArg (fun h : b ⟶ c => h.index i) hfst
  · exact congrArg (fun h : b ⟶ r.toFiniteCover => h.index i) hsnd

/-- The common refinement with its actual two projections. -/
def rationalProductFan (c : FiniteCover U) (r : FiniteRationalCover U) :
    BinaryFan c r.toFiniteCover :=
  BinaryFan.mk (c.rationalProductFst r) (c.rationalProductSnd r)

/-- The mixed common refinement is a binary product in the category retaining
chosen refinement indices and actual bounded restrictions. -/
def rationalProductFanIsLimit (c : FiniteCover U) (r : FiniteRationalCover U) :
    IsLimit (c.rationalProductFan r) :=
  BinaryFan.isLimitMk
    (fun s => rationalProductLift s.fst s.snd)
    (fun s => rationalProductLift_fst s.fst s.snd)
    (fun s => rationalProductLift_snd s.fst s.snd)
    (fun s _m hfst hsnd => rationalProduct_hom_ext
      (hfst.trans (rationalProductLift_fst s.fst s.snd).symm)
      (hsnd.trans (rationalProductLift_snd s.fst s.snd).symm))

/-- The product construction acts on arbitrary chosen refinements of both
supplied covers, using the full-test lift for the new component restrictions. -/
def rationalProductMap {b c : FiniteCover U} {r s : FiniteRationalCover U}
    (f : b ⟶ c) (g : r.toFiniteCover ⟶ s.toFiniteCover) :
    b.rationalProduct r ⟶ c.rationalProduct s :=
  rationalProductLift (b.rationalProductFst r ≫ f) (b.rationalProductSnd r ≫ g)

@[simp] theorem rationalProductMap_fst {b c : FiniteCover U}
    {r s : FiniteRationalCover U} (f : b ⟶ c) (g : r.toFiniteCover ⟶ s.toFiniteCover) :
    rationalProductMap f g ≫ c.rationalProductFst s = b.rationalProductFst r ≫ f :=
  rationalProductLift_fst _ _

@[simp] theorem rationalProductMap_snd {b c : FiniteCover U}
    {r s : FiniteRationalCover U} (f : b ⟶ c) (g : r.toFiniteCover ⟶ s.toFiniteCover) :
    rationalProductMap f g ≫ c.rationalProductSnd s = b.rationalProductSnd r ≫ g :=
  rationalProductLift_snd _ _

@[simp] theorem rationalProductMap_id (c : FiniteCover U) (r : FiniteRationalCover U) :
    rationalProductMap (𝟙 c) (𝟙 r.toFiniteCover) = 𝟙 (c.rationalProduct r) := by
  apply rationalProduct_hom_ext <;> simp

theorem rationalProductMap_comp {a b c : FiniteCover U}
    {r s t : FiniteRationalCover U}
    (f : a ⟶ b) (f' : b ⟶ c)
    (g : r.toFiniteCover ⟶ s.toFiniteCover) (g' : s.toFiniteCover ⟶ t.toFiniteCover) :
    rationalProductMap (f ≫ f') (g ≫ g') =
      rationalProductMap f g ≫ rationalProductMap f' g' := by
  apply rationalProduct_hom_ext
  · simp only [Category.assoc, rationalProductMap_fst]
    rw [← Category.assoc (rationalProductMap f g), rationalProductMap_fst, Category.assoc]
  · simp only [Category.assoc, rationalProductMap_snd]
    rw [← Category.assoc (rationalProductMap f g), rationalProductMap_snd, Category.assoc]

/-- The first projection retains the actual finite disjoint unions of spectra
and commutes with their original maps to the target locus. -/
theorem rationalProduct_totalMap_fst (c : FiniteCover U) (r : FiniteRationalCover U) :
    c.totalMap.comp (c.rationalProductFst r).spectrumMap =
      (c.rationalProduct r).totalMap :=
  (c.rationalProductFst r).spectrumMap_over_target

/-- The rational-cover projection gives the same actual total spectrum map
to the target locus. -/
theorem rationalProduct_totalMap_snd (c : FiniteCover U) (r : FiniteRationalCover U) :
    r.toFiniteCover.totalMap.comp (c.rationalProductSnd r).spectrumMap =
      (c.rationalProduct r).totalMap :=
  (c.rationalProductSnd r).spectrumMap_over_target

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
