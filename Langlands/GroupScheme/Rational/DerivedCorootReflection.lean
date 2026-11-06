import Langlands.GroupScheme.CentralIsogeny.CorootCompatibility
import Langlands.GroupScheme.Rational.DerivedRootTransport
import Langlands.GroupScheme.Rational.CentralTorusFixedness

/-! # Actual reflection transport through a central torus complement -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem reflectionProduct_postcomp {B : Scheme.{u}} {X Y H K : GroupScheme B}
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

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G)
    (hsquare : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    [hpflat : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

include hsquare hpflat hpsurj hc in
/-- A source reflection becomes the explicit ambient reflection when a flat,
surjective product supplies a central complement on which the ambient root vanishes. -/
theorem IsNormalizingPoint.map_latticeReflectionIso_of_centralComplement
    {α : characterLattice T} {β : characterLattice S} {ν : cocharacterLattice T}
    (h : latticePairing T α ν = 2) (h' : latticePairing S β (ν ≫ e) = 2)
    (hroot : e ≫ β = α) (hzero : c ≫ β = 0)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D.X}
    (hn : IsNormalizingPoint j n (latticeReflectionIso α ν h)) :
    IsNormalizingPoint i (n ≫ d.hom.hom) (latticeReflectionIso β (ν ≫ e) h') := by
  let r := latticeReflectionIso α ν h
  let r' := latticeReflectionIso β (ν ≫ e) h'
  have he : CommGroupScheme.groupHom r.hom ≫ CommGroupScheme.groupHom e =
      CommGroupScheme.groupHom e ≫ CommGroupScheme.groupHom r'.hom :=
    congrArg CommGroupScheme.groupHom (latticeReflectionIso_hom_comp e α β ν h h' hroot)
  have hret : CommGroupScheme.groupHom e ≫ (i ≫ (G.innerIso (n ≫ d.hom.hom)).hom) =
      CommGroupScheme.groupHom e ≫ (CommGroupScheme.groupHom r'.hom ≫ i) := by
    calc
      _ = j ≫ d ≫ (G.innerIso (n ≫ d.hom.hom)).hom := by
        rw [← Category.assoc, ← hsquare, Category.assoc]
      _ = (j ≫ (D.innerIso n).hom) ≫ d := by
        rw [Category.assoc, innerIso_hom_comp]
      _ = (CommGroupScheme.groupHom r.hom ≫ j) ≫ d :=
        congrArg (fun f => f ≫ d) hn
      _ = (CommGroupScheme.groupHom r.hom ≫ CommGroupScheme.groupHom e) ≫ i := by
        rw [Category.assoc, hsquare, ← Category.assoc]
      _ = _ := by rw [he, Category.assoc]
  have hfix : c ≫ r'.hom = c := by
    simp only [r', latticeReflectionIso_hom, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, hzero, Limits.zero_comp, sub_zero]
  have hcen : CommGroupScheme.groupHom c ≫ (i ≫ (G.innerIso (n ≫ d.hom.hom)).hom) =
      CommGroupScheme.groupHom c ≫ (CommGroupScheme.groupHom r'.hom ≫ i) := by
    rw [← Category.assoc, hc.comp_innerIso_hom]
    have hh := congrArg CommGroupScheme.groupHom hfix
    change CommGroupScheme.groupHom c ≫ CommGroupScheme.groupHom r'.hom =
      CommGroupScheme.groupHom c at hh
    rw [← Category.assoc, hh]
  let p := RelativeRoot.centralComplementProduct e c
  have hp : p ≫ (i ≫ (G.innerIso (n ≫ d.hom.hom)).hom) =
      p ≫ (CommGroupScheme.groupHom r'.hom ≫ i) := by
    dsimp only [p, RelativeRoot.centralComplementProduct]
    rw [reflectionProduct_postcomp, reflectionProduct_postcomp]
    simp only [hret, hcen]
  have : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
  have : Epi p.hom.hom := Over.epi_of_epi_left _
  apply Grp.hom_ext
  apply (cancel_epi p.hom.hom).mp
  exact congrArg (fun f => f.hom.hom) hp

variable [IsAffineHom D.X.hom] {J : Type v}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

include hsquare hpflat hpsurj hc in
/-- An actual source root datum supplies a normalizing point for each ambient
reflection whose root restricts to the chosen source root and vanishes on the complement. -/
theorem IsRootDatumOf.exists_normalizing_latticeReflectionIso_of_centralComplement
    (hP : IsRootDatumOf j P) (hT : IsSplitTorus T.toGrp)
    (a : J) (β : characterLattice S) (hroot : e ≫ β = P.root a)
    (hzero : c ≫ β = 0) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      IsNormalizingPoint i n (latticeReflectionIso β (P.coroot a ≫ e)
        (by
          change gmEndEquiv k ((P.coroot a ≫ e) ≫ β) = 2
          rw [Category.assoc, hroot]
          change latticePairing T (P.root a) (P.coroot a) = 2
          rw [← hP.1]
          exact P.root_coroot_two a)) := by
  obtain ⟨n, hn⟩ := hP.exists_normalizing_latticeReflectionIso j hT a
  exact ⟨n ≫ d.hom.hom,
    hn.map_latticeReflectionIso_of_centralComplement e c j i d hsquare hc
      _ _ hroot hzero⟩

/-- Choose an actual ambient point realizing the transported source reflection. -/
def normalizingLatticeReflectionOfCentralComplement
    (hP : IsRootDatumOf j P) (hT : IsSplitTorus T.toGrp)
    (a : J) (β : characterLattice S) (hroot : e ≫ β = P.root a)
    (hzero : c ≫ β = 0) :
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      IsNormalizingPoint i n (latticeReflectionIso β (P.coroot a ≫ e)
        (by
          change gmEndEquiv k ((P.coroot a ≫ e) ≫ β) = 2
          rw [Category.assoc, hroot]
          change latticePairing T (P.root a) (P.coroot a) = 2
          rw [← hP.1]
          exact P.root_coroot_two a))} :=
  ⟨Classical.choose (hP.exists_normalizing_latticeReflectionIso_of_centralComplement
    e c j i d hsquare hc hT a β hroot hzero),
    Classical.choose_spec (hP.exists_normalizing_latticeReflectionIso_of_centralComplement
      e c j i d hsquare hc hT a β hroot hzero)⟩

end Langlands.GroupScheme
