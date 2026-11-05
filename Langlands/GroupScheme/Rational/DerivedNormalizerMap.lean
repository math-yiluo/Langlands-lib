import Langlands.GroupScheme.Rational.DerivedCoverNormalizerLift
import Langlands.GroupScheme.Rational.DerivedRootTransport
import Langlands.GroupScheme.Rational.CentralTorusFixedness
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Original normalizer images through a supplied central torus product -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem prodHom_postcomp {B : Scheme.{u}} {X Y H K : GroupScheme B}
    (f : X ⟶ H) (g : Y ⟶ H)
    (hfg : ∀ (U : Over B) (x : U ⟶ X.X) (y : U ⟶ Y.X),
      Commute (x ≫ f.hom.hom) (y ≫ g.hom.hom))
    (a : H ⟶ K) :
    prodHom f g hfg ≫ a =
      prodHom (f ≫ a) (g ≫ a) (fun U x y =>
        (hfg U x y).map ((yonedaGrp.map a).app (Opposite.op U)).hom) := by
  apply hom_ext_points
  intro U x
  simp only [Grp.comp_hom_hom, ← Category.assoc, comp_prodHom, MonObj.mul_comp]

private theorem factorHom_of_effectiveEpi {B : Scheme.{u}}
    {P S G : GroupScheme B} (p q : P ⟶ S) (i a : S ⟶ G)
    [EffectiveEpi p.hom.hom.left] [Mono i.hom.hom.left]
    (h : q ≫ i = p ≫ a) : ∃ b : S ⟶ S, b ≫ i = a := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have sq : CommSq q.hom.hom.left p.hom.hom.left i.hom.hom.left a.hom.hom.left :=
    ⟨congrArg (fun f => f.hom.hom.left) h⟩
  let k : S.X ⟶ S.X := Over.homMk sq.lift (by
    calc
      sq.lift ≫ S.X.hom = sq.lift ≫ i.hom.hom.left ≫ G.X.hom := by
        rw [Over.w i.hom.hom]
      _ = a.hom.hom.left ≫ G.X.hom := by rw [← Category.assoc, sq.fac_right]
      _ = S.X.hom := Over.w a.hom.hom)
  have hk : k ≫ i.hom.hom = a.hom.hom := Over.OverMorphism.ext sq.fac_right
  let f (U : Over B) : (U ⟶ S.X) →* (U ⟶ S.X) :=
    { toFun := fun x => x ≫ k
      map_one' := by
        apply (cancel_mono i.hom.hom).mp
        simp only [Category.assoc, hk, MonObj.one_comp]
      map_mul' := fun x y => by
        apply (cancel_mono i.hom.hom).mp
        simp only [Category.assoc, hk, MonObj.mul_comp] }
  have hnat {U V : Over B} (v : U ⟶ V) (x : V ⟶ S.X) :
      f U (v ≫ x) = v ≫ f V x := Category.assoc v x k
  refine ⟨homOfPoints f hnat, ?_⟩
  apply hom_ext_points
  intro U x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_homOfPoints]
  exact (Category.assoc x k i.hom.hom).trans (congrArg (x ≫ ·) hk)

namespace DerivedNormalizerMap

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp)
    (hi : IsMaximalSplitTorus i)
    [hpflat : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

include hpflat hpsurj h hT hA hi hc in
/-- A point normalizing the retained torus maps to a point normalizing the
ambient maximal split torus, using the supplied central torus product. -/
theorem map_mem_normalizerPoints (n : normalizerPoints j) :
    rationalPoints.map d n.val ∈ normalizerPoints i := by
  obtain ⟨σ, hσ⟩ := n.property
  let g := rationalPoints.map d n.val
  let a := i ≫ (G.innerIso g).hom
  let p := RelativeRoot.centralComplementProduct e c
  let q := RelativeRoot.centralComplementProduct (σ.hom ≫ e) c
  have hret : CommGroupScheme.groupHom e ≫ a =
      CommGroupScheme.groupHom (σ.hom ≫ e) ≫ i := by
    calc
      _ = j ≫ d ≫ (G.innerIso g).hom := by
        dsimp only [a]
        rw [← Category.assoc, ← h, Category.assoc]
      _ = (j ≫ (D.innerIso n.val).hom) ≫ d := by
        rw [Category.assoc, innerIso_hom_comp]
        rfl
      _ = CommGroupScheme.groupHom σ.hom ≫ j ≫ d := by
        rw [hσ, Category.assoc]
      _ = _ := by
        rw [h]
        rfl
  have hcen : CommGroupScheme.groupHom c ≫ a = CommGroupScheme.groupHom c ≫ i := by
    simpa only [a, ← Category.assoc] using hc.comp_innerIso_hom g
  have hsq : q ≫ i = p ≫ a := by
    dsimp only [q, p, RelativeRoot.centralComplementProduct]
    rw [prodHom_postcomp, prodHom_postcomp]
    simp only [hret, hcen]
  have : IsAffineHom (T.toGrp ⊗ A.toGrp).X.hom := (hT.tensor hA).isAffineHom
  have : IsAffine (T.toGrp ⊗ A.toGrp).X.left :=
    isAffine_of_isAffineHom (T.toGrp ⊗ A.toGrp).X.hom
  have : IsAffineHom S.X.hom := hi.isSplitSubtorus.1.isAffineHom
  have : IsAffine S.X.left := isAffine_of_isAffineHom S.X.hom
  have : QuasiCompact p.hom.hom.left := inferInstance
  have : Flat p.hom.hom.left := hpflat
  have : Surjective p.hom.hom.left := hpsurj
  have : EffectiveEpi p.hom.hom.left := inferInstance
  have : IsClosedImmersion i.hom.hom.left := hi.isSplitSubtorus.2
  obtain ⟨b, hb⟩ := factorHom_of_effectiveEpi p q i a hsq
  have : IsIso b := (hi.comp_iso (G.innerIso g)).2 S i hi.1 b hb
  let τ : S ≅ S :=
    { hom := Additive.ofMul (asIso b).hom
      inv := Additive.ofMul (asIso b).inv
      hom_inv_id := congrArg Additive.ofMul (asIso b).hom_inv_id
      inv_hom_id := congrArg Additive.ofMul (asIso b).inv_hom_id }
  exact ⟨τ, hb.symm⟩

/-- The original rational-point map, with codomain restricted to the ambient
normalizer under the supplied central product. -/
def normalizerPointsHom : normalizerPoints j →* normalizerPoints i where
  toFun n := ⟨rationalPoints.map d n.val,
    map_mem_normalizerPoints e c j i d h hT hA hi hc n⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' n m := Subtype.ext (map_mul _ n.val m.val)

@[simp]
theorem normalizerPointsHom_coe (n : normalizerPoints j) :
    (normalizerPointsHom e c j i d h hT hA hi hc n : rationalPoints G) =
      rationalPoints.map d n.val := rfl

end DerivedNormalizerMap

end Langlands.GroupScheme
