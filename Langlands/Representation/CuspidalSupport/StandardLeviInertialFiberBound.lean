import Langlands.Representation.CuspidalSupport.StandardLeviInertialClass
import Langlands.Representation.Exponents.FiniteNormalizerRepresentatives
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof
import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry

/-! # Uniform finite fibers of the standard Levi map on inertial classes -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local notation "j" => fun I => Standard.leviHom i ν (rootSet i ν I)

local instance fiberAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance fiberLeviClosed (I : Finset (SimpleRoot i ν)) : IsClosedImmersion (j I).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance fiberLeviAffine (I : Finset (SimpleRoot i ν)) : IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (j I).hom.hom.left
local instance fiberLeviFiniteType (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (j I).hom.hom.w]
  infer_instance

/-- A single finite list of rational normalizer representatives for each standard Levi. -/
theorem standardLevi_exists_finite_normalizer_representatives
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    ∃ (n : ℕ) (g : Fin n → rationalPoints G),
      ∀ (w : rationalPoints G) (e : bernsteinLeviScheme i ν I ≅ bernsteinLeviScheme i ν I),
        e.hom ≫ j I = j I ≫ (G.innerIso w).hom →
          ∃ (t : Fin n) (m : rationalPoints (bernsteinLeviScheme i ν I)),
            w = g t * rationalPoints.map (j I) m := by
  obtain ⟨hM, A, a, _, ha, _⟩ := standardLeviSplitComponentStatement F G hG T i hi ν hν
    (rootSet i ν I) (rootSet_subset i ν I)
  have := hM.isAffineHom
  obtain ⟨ζ, hζ⟩ := StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer
    hG hi.isSplitSubtorus.1 i ν (rootSet i ν I)
  have hj := Standard.isRepresentedBy_leviHom i ν (rootSet i ν I)
  rw [hζ] at hj
  have hZ := ha.torusCentralizer_comp_eq_of_dynamicCentralizer
    (CommGroupScheme.groupHom ζ ≫ i) hj
  obtain ⟨n, g, _, hg⟩ := ha.exists_finite_normalizer_representatives
    (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)) hZ
  exact ⟨n, g, hg⟩

omit [LocallyOfFiniteType G.X.hom] in
private theorem rationalLeviConjugacy_conj_map {I K : Finset (SimpleRoot i ν)}
    (c : RationalLeviConjugacy (j I) (j K))
    (m : rationalPoints (bernsteinLeviScheme i ν I)) :
    c.point * rationalPoints.map (j I) m * c.point⁻¹ =
      rationalPoints.map (j K) (rationalPoints.map c.iso.hom m) := by
  have hleft : rationalPoints.map (j I ≫ (G.innerIso c.point).hom) m =
      rationalPoints.map (G.innerIso c.point).hom (rationalPoints.map (j I) m) := by
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  have hright : rationalPoints.map (c.iso.hom ≫ j K) m =
      rationalPoints.map (j K) (rationalPoints.map c.iso.hom m) := by
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  rw [← hright, ← c.commutes, hleft, rationalPoints_map_innerIso]
  rfl

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

local instance fiberAmbientTopology : TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

private theorem fiber_embedding_of_normalizer_representatives
    (J : Finset (SimpleRoot i ν)) (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    {n : ℕ} (g : Fin n → rationalPoints G)
    (hg : ∀ (w : rationalPoints G)
        (e : bernsteinLeviScheme i ν a.roots ≅ bernsteinLeviScheme i ν a.roots),
      e.hom ≫ j a.roots = j a.roots ≫ (G.innerIso w).hom →
        ∃ (t : Fin n) (m : rationalPoints (bernsteinLeviScheme i ν a.roots)),
          w = g t * rationalPoints.map (j a.roots) m) :
    Nonempty ({b // standardLeviInertialToAmbient i ν family J b =
      bernsteinInertialClass i ν family a} ↪ (Finset (SimpleRoot i ν) × Fin n)) := by
  classical
  let Transporter (K : Finset (SimpleRoot i ν)) := RationalLeviConjugacy (j a.roots) (j K)
  let base (K : Finset (SimpleRoot i ν)) (c : Transporter K) : Transporter K :=
    Classical.choice ⟨c⟩
  have hnorm (K) (c : Transporter K) :
      ∃ (t : Fin n) (m : rationalPoints (bernsteinLeviScheme i ν a.roots)),
        c.point = (base K c).point * g t * rationalPoints.map (j a.roots) m := by
    let d := c.trans (base K c).symm
    obtain ⟨t, m, hm⟩ := hg d.point d.iso d.commutes.symm
    change (base K c).point⁻¹ * c.point = _ at hm
    exact ⟨t, m, by rw [mul_assoc, ← hm, mul_inv_cancel_left]⟩
  choose label m hm using hnorm
  have hconjMem {K L} (c : Transporter K) (d : Transporter L) (hK : K ⊆ J)
      (he : (K, label K c) = (L, label L d)) : (c.symm.trans d).point ∈ levi i ν J := by
    have hKL : K = L := congrArg Prod.fst he
    subst L
    have ht : label K c = label K d := congrArg Prod.snd he
    have hpt : d.point = c.point * rationalPoints.map (j a.roots) ((m K c)⁻¹ * m K d) := by
      have hc := hm K c
      have hd := hm K d
      have hbase : (base K d).point = (base K c).point := rfl
      simp only [hd, hc, hbase, ht, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
    apply levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter K J hK
    change d.point * c.point⁻¹ ∈ levi i ν K
    rw [hpt, rationalLeviConjugacy_conj_map i ν c]
    change _ ∈ (standardLevi i ν (rootSet i ν K)).rationalPoints
    rw [SubgroupFunctor.rationalPoints_eq_range (Standard.isRepresentedBy_leviHom i ν _)]
    exact ⟨_, rfl⟩
  let Fiber := {b // standardLeviInertialToAmbient i ν family J b =
    bernsteinInertialClass i ν family a}
  let rep (b : Fiber) : StandardLeviCuspidalDatum.{uF, uV} i ν family J := Quotient.out b.val
  have hrep (b : Fiber) : standardLeviInertialClass i ν family (rep b) = b.val :=
    Quotient.out_eq b.val
  have hrelated (b : Fiber) : IsBernsteinInertiaRelated i ν family a (rep b).val := by
    apply (bernsteinInertialClass_eq_iff i ν family _ _).mp
    rw [← standardLeviInertialToAmbient_class, hrep, b.property]
  let c (b : Fiber) : Transporter (rep b).val.roots := (hrelated b).choose
  refine ⟨⟨fun b => ((rep b).val.roots, label _ (c b)), ?_⟩⟩
  intro b d he
  apply Subtype.ext
  rw [← hrep b, ← hrep d, standardLeviInertialClass_eq_iff]
  have hb := (hrelated b).choose_spec
  have hd := (hrelated d).choose_spec
  have hback := ((rationalInertiaRelated_pullback_iff (c b).iso _ _).mp hb).symm
  exact ⟨(c b).symm.trans (c d), hconjMem (c b) (c d) (rep b).property he,
    (hback.trans (hd.rationalIsoPullback (c b).iso.symm)).trans
      (IsRationalInertiaRelated.of_iso
        (rationalIsoPullbackTransIso (c b).iso.symm (c d).iso (rep d).val.representation))⟩

/-- The fibers of the map on inertial classes from any standard Levi admit a common finite bound. -/
def StandardLeviInertialFiberBoundStatement : Prop :=
  ∃ B : ℕ, ∀ (J : Finset (SimpleRoot i ν)) (s : BernsteinInertialClass.{uF, uV} i ν family),
    Nonempty ({b // standardLeviInertialToAmbient i ν family J b = s} ↪ Fin B)

/-- Bound the fibers by the number of standard Levi labels times a common normalizer bound. -/
theorem standardLeviInertialFiberBound : StandardLeviInertialFiberBoundStatement.{uF, uV} i ν family := by
  classical
  let := family.finiteSimpleRoots
  let := Fintype.ofFinite (SimpleRoot i ν)
  have hn (I) := standardLevi_exists_finite_normalizer_representatives i ν
    family.connectedReductive family.maximalSplitTorus family.genericCocharacter I
  choose n g hg using hn
  let N := Finset.univ.sup n
  let L := Finset (SimpleRoot i ν) × Fin N
  refine ⟨Fintype.card L, fun J s => ?_⟩
  let a := Quotient.out s
  have ha : bernsteinInertialClass i ν family a = s := Quotient.out_eq s
  rw [← ha]
  obtain ⟨e⟩ := fiber_embedding_of_normalizer_representatives i ν family J a
    (g a.roots) (hg a.roots)
  have hle : n a.roots ≤ N := Finset.le_sup (Finset.mem_univ a.roots)
  exact ⟨(e.trans ((Function.Embedding.refl _).prodMap (Fin.castLEEmb hle))).trans
    (Fintype.equivFin L).toEmbedding⟩

end Langlands.CuspidalSupport
