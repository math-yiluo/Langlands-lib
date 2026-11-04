import Langlands.GroupScheme.Rational.LeviCentralizerExtension
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement

/-! # The central torus of a Levi adapted to a radical intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {B : Scheme.{u}} {A L G : GroupScheme B} {T : CommGroupScheme B}
  {a : A ⟶ L}

/-- A central subgroup of a containing group centralizes every commutative
subgroup that factors through that group, after mapping to the ambient group. -/
theorem IsCentral.range_comp_le_torusCentralizer_of_factor
    (ha : IsCentral a) (j : L ⟶ G) (t : T.toGrp ⟶ G)
    (f : T.toGrp ⟶ L) (hf : f ≫ j = t) :
    SubgroupFunctor.range (a ≫ j) ≤ torusCentralizer t := by
  intro U x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  intro V q z
  have hc := ha U y V q (z ≫ f.hom.hom)
  have he := congrArg (fun w : V ⟶ L.X => w ≫ j.hom.hom) hc.eq
  apply (commute_iff_eq _ _).mpr
  simpa only [← hf, Grp.comp_hom_hom, MonObj.mul_comp, Category.assoc] using he

end Base

section Field

variable {k : Type u} [Field k]
  {G P L R : GroupScheme (Spec (CommRingCat.of k))}
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {j : P ⟶ G} {l : L ⟶ P} {r : R ⟶ P}
  {t : T.toGrp ⟶ G} {f : T.toGrp ⟶ P}
  {sT : S.toGrp ⟶ T.toGrp} {sL : S.toGrp ⟶ L}

/-- For an actual Levi representing the centralizer of a supplied radical
intersection, self-centralization of the ambient torus makes that intersection
the largest closed central subtorus of the Levi. -/
theorem IsRationalLeviSubgroup.isLargestCentralSubtorus_of_radicalIntersection
    (hl : IsRationalLeviSubgroup l) (hj : IsClosedSubgroup j)
    (ht : IsClosedSubgroup t) (hfactor : f ≫ j = t)
    (hR : IsSolvableRadical r) (hS : IsTorus S.toGrp)
    (hsT : IsClosedSubgroup sT)
    (hintersection : SubgroupFunctor.range (sT ≫ f) =
      SubgroupFunctor.range f ⊓ SubgroupFunctor.range r)
    (hcentralizer : (torusCentralizer (sT ≫ t)).IsRepresentedBy (l ≫ j))
    (hsL : sL ≫ l = sT ≫ f)
    (hself : torusCentralizer t = SubgroupFunctor.range t) :
    IsLargestCentralSubtorus sL := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  have hjmono : Mono j.hom.hom := Over.mono_of_mono_left _
  have hlmono : Mono l.hom.hom := Over.mono_of_mono_left _
  have hfclosed : IsClosedSubgroup f :=
    IsClosedSubgroup.of_comp hj (by rw [hfactor]; exact ht)
  have hsLambient : sL ≫ (l ≫ j) = sT ≫ t := by
    rw [← Category.assoc, hsL, Category.assoc, hfactor]
  have hsLclosed : IsClosedSubgroup sL := by
    apply IsClosedSubgroup.of_comp hl.isClosedSubgroup
    rw [hsL]
    let : IsClosedImmersion sT.hom.hom.left := hsT
    let : IsClosedImmersion f.hom.hom.left := hfclosed
    change IsClosedImmersion (sT.hom.hom.left ≫ f.hom.hom.left)
    infer_instance
  have hsLcentral : IsCentral sL := by
    apply isCentral_of_range_le_torusCentralizer hcentralizer.1
    rw [hsLambient]
    exact hcentralizer.2.le
  refine ⟨hS, hsLclosed, hsLcentral, ?_⟩
  intro A a hA ha hca
  have htcentralizer : SubgroupFunctor.range t ≤ torusCentralizer (sT ≫ t) :=
    (range_le_torusCentralizer t).trans
      (torusCentralizer_le_of_factor t (sT ≫ t) sT rfl)
  let tL : T.toGrp ⟶ L := hcentralizer.factorHom t htcentralizer
  have htL : tL ≫ (l ≫ j) = t := hcentralizer.factorHom_comp t htcentralizer
  have haT : SubgroupFunctor.range (a ≫ l) ≤ SubgroupFunctor.range f := by
    apply (SubgroupFunctor.range_comp_le_iff_of_mono (a ≫ l) f j hjmono).mp
    rw [hfactor, Category.assoc]
    rw [← hself]
    exact hca.range_comp_le_torusCentralizer_of_factor (l ≫ j) t tL htL
  have haR : SubgroupFunctor.range (a ≫ l) ≤ SubgroupFunctor.range r :=
    hl.range_centralTorus_le_solvableRadical a hR hA ha hca
  apply (SubgroupFunctor.range_comp_le_iff_of_mono a sL l hlmono).mp
  rw [hsL, hintersection]
  exact fun U x hx => ⟨haT U hx, haR U hx⟩

/-- The canonical centralizer factor of a supplied radical intersection, with
its actual factorization through the Levi and its largest-central-torus property. -/
def IsRationalLeviSubgroup.radicalIntersectionCenter
    (hl : IsRationalLeviSubgroup l) (hj : IsClosedSubgroup j)
    (ht : IsClosedSubgroup t) (hfactor : f ≫ j = t)
    (hR : IsSolvableRadical r) (hS : IsTorus S.toGrp)
    (hsT : IsClosedSubgroup sT)
    (hintersection : SubgroupFunctor.range (sT ≫ f) =
      SubgroupFunctor.range f ⊓ SubgroupFunctor.range r)
    (hcentralizer : (torusCentralizer (sT ≫ t)).IsRepresentedBy (l ≫ j))
    (hself : torusCentralizer t = SubgroupFunctor.range t) :
    {sL : S.toGrp ⟶ L // sL ≫ l = sT ≫ f ∧ IsLargestCentralSubtorus sL} := by
  let sL := torusCentralizerFactor (sT ≫ t) hcentralizer
  let : IsClosedImmersion j.hom.hom.left := hj
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hsL : sL ≫ l = sT ≫ f := by
    apply hjrep.hom_ext
    change (torusCentralizerFactor (sT ≫ t) hcentralizer ≫ l) ≫ j =
      (sT ≫ f) ≫ j
    rw [Category.assoc, torusCentralizerFactor_comp, Category.assoc, hfactor]
  exact ⟨sL, hsL, hl.isLargestCentralSubtorus_of_radicalIntersection
    hj ht hfactor hR hS hsT hintersection hcentralizer hsL hself⟩

/-- The published maximal-torus centralizer proposition supplies the local
self-centralizing equality used in the preceding construction. -/
theorem IsRationalLeviSubgroup.isLargestCentralSubtorus_of_structural_input
    (hmaximal : MaximalTorusCentralizerStatement.{u})
    (hG : IsConnectedReductive G)
    (hl : IsRationalLeviSubgroup l) (hj : IsClosedSubgroup j)
    (ht : IsMaximalTorus t) (hfactor : f ≫ j = t)
    (hR : IsSolvableRadical r) (hS : IsTorus S.toGrp)
    (hsT : IsClosedSubgroup sT)
    (hintersection : SubgroupFunctor.range (sT ≫ f) =
      SubgroupFunctor.range f ⊓ SubgroupFunctor.range r)
    (hcentralizer : (torusCentralizer (sT ≫ t)).IsRepresentedBy (l ≫ j))
    (hsL : sL ≫ l = sT ≫ f) :
    IsLargestCentralSubtorus sL :=
  hl.isLargestCentralSubtorus_of_radicalIntersection hj ht.2.1 hfactor
    hR hS hsT hintersection hcentralizer hsL (hmaximal k G hG T t ht)

end Field

end Langlands.GroupScheme
