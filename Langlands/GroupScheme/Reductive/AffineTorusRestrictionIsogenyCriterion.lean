import Langlands.GroupScheme.Reductive.TorusRestrictionIsogenyCriterion
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.FibrewiseIsogenyProof

/-! # An affine-base isogeny criterion from a compatible torus isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {I I' : Type u} [Fintype I] [Fintype I']
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    {J J' : Type u} [Finite J] [Finite J']
    {P : RootDatum J (I → ℤ) (I → ℤ)}
    {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hQ : IsFibrewiseRootDatumOf I' H i' Q)

local instance affineCriterionFieldSource (k : Type u) [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap R k)))

local instance affineCriterionFieldTarget (k : Type u) [Field k] [Algebra R k] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj H).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd H.X.hom (algebraBaseMap R k)))

include hP hQ

/-- The specified compatible homomorphism is an isogeny on every supplied
field algebra when its torus restriction is an isogeny and the fixed
coordinate root data have equal root counts. -/
theorem isIsogeny_algebraMap_of_split_torus_restriction_of_root_card_eq
    (hG : IsReductive G) (hH : IsReductive H)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hi' : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I') i')
    (q : G ⟶ H)
    (t : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hit : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (hcard : Nat.card J = Nat.card J')
    (k : Type u) [Field k] [Algebra R k] :
    IsIsogeny ((baseChange (algebraBaseMap R k)).map q) := by
  let : Smooth G.X.hom := hG.smooth
  let : Smooth H.X.hom := hH.smooth
  let b := algebraBaseMap R k
  let B := baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom b))
  let : IsAffineHom (B.obj H).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd H.X.hom b))
  let e := splitTorus.baseChangeIso b I
  let e' := splitTorus.baseChangeIso b I'
  let tk : splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I' :=
    Additive.ofMul (e.inv ≫ B.map (CommGroupScheme.groupHom t) ≫ e'.hom)
  have htk : IsIsogeny (CommGroupScheme.groupHom tk) :=
    (isIsogeny_of_isIso e.inv).comp
      ((ht.baseChange b).comp (isIsogeny_of_isIso e'.hom))
  have hsquare :
      splitTorus.baseChangeHom (K := k) G I i ≫ B.map q =
        CommGroupScheme.groupHom tk ≫
          splitTorus.baseChangeHom (K := k) H I' i' := by
    change (e.inv ≫ B.map i) ≫ B.map q =
      (e.inv ≫ B.map (CommGroupScheme.groupHom t) ≫ e'.hom) ≫
        (e'.inv ≫ B.map i')
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← B.map_comp, hit, B.map_comp]
  exact isIsogeny_of_torus_restriction_of_root_card_eq
    (k := k) (G := B.obj G) (H := B.obj H)
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I')
    (P := CoordinateRootDatum.fieldRealization k P)
    (Q := CoordinateRootDatum.fieldRealization k Q)
    (hG.isConnectedReductive_baseChange b) (hH.isConnectedReductive_baseChange b)
    (B.map q) (isSplitTorus_splitTorus I) (isSplitTorus_splitTorus I')
    (splitTorus.baseChangeHom (K := k) G I i)
    (splitTorus.baseChangeHom (K := k) H I' i') tk
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hi k)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I' H i' hi' k)
    htk hsquare (hP.field k) (hQ.field k) hcard

/-- The actual schematic image of every supplied field-algebra pullback
is its target under the compatible torus-isogeny and equal-root-count
hypotheses. The forward map is the canonical image inclusion. -/
def fieldImageIsoOfSplitTorusRestriction
    (hG : IsReductive G) (hH : IsReductive H)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hi' : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I') i')
    (q : G ⟶ H)
    (t : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hit : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (hcard : Nat.card J = Nat.card J')
    (k : Type u) [Field k] [Algebra R k] :
    SchematicImage.image ((baseChange (algebraBaseMap R k)).map q) ≅
      (baseChange (algebraBaseMap R k)).obj H := by
  let B := baseChange (algebraBaseMap R k)
  let : Smooth (B.obj G).X.hom :=
    (hG.isConnectedReductive_baseChange (algebraBaseMap R k)).smooth
  let : Smooth (B.obj H).X.hom :=
    (hH.isConnectedReductive_baseChange (algebraBaseMap R k)).smooth
  let : ConnectedSpace (B.obj G).X.left :=
    (hG.isConnectedReductive_baseChange (algebraBaseMap R k)).connectedSpace
  let : ConnectedSpace (B.obj H).X.left :=
    (hH.isConnectedReductive_baseChange (algebraBaseMap R k)).connectedSpace
  have hq := isIsogeny_algebraMap_of_split_torus_restriction_of_root_card_eq
    i i' hP hQ hG hH hi hi' q t ht hit hcard k
  let : IsFinite (B.map q).hom.hom.left := hq.1
  exact imageIsoOfFiniteFinrankEq (B.map q)
    (Lie.finrank_kernel_eq_of_isogeny (B.map q) hq)

@[simp] theorem fieldImageIsoOfSplitTorusRestriction_hom
    (hG : IsReductive G) (hH : IsReductive H)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hi' : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I') i')
    (q : G ⟶ H)
    (t : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hit : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (hcard : Nat.card J = Nat.card J')
    (k : Type u) [Field k] [Algebra R k] :
    (fieldImageIsoOfSplitTorusRestriction
      i i' hP hQ hG hH hi hi' q t ht hit hcard k).hom =
      SchematicImage.inclusion ((baseChange (algebraBaseMap R k)).map q) := rfl

/-- For reductive groups over any affine base, a compatible torus isogeny and
equal root counts in the supplied fibrewise root data make the specified
ambient homomorphism an isogeny. -/
theorem isIsogeny_of_split_torus_restriction_of_fibrewise_root_card_eq
    (hG : IsReductive G) (hH : IsReductive H)
    (hi : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hi' : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I') i')
    (q : G ⟶ H)
    (t : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hit : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (hcard : Nat.card J = Nat.card J') : IsIsogeny q := by
  apply reductiveFibrewiseIsogeny (Spec (CommRingCat.of R)) G H hG hH q
  intro s
  let k := (Spec (CommRingCat.of R)).residueField s
  let b := (Spec (CommRingCat.of R)).fromSpecResidueField s
  let : Algebra R k := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap R k = b := Spec.map_preimage b
  have h := isIsogeny_algebraMap_of_split_torus_restriction_of_root_card_eq
    i i' hP hQ hG hH hi hi' q t ht hit hcard k
  rwa [hb] at h

end Langlands.GroupScheme
