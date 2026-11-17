import Langlands.GroupScheme.Reductive.GeometricRootDatumComparison
import Langlands.GroupScheme.Reductive.RootDatumGaloisSimpleRoots
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Root-datum comparisons respecting supplied Borel chambers -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace RootPairing.Base

variable {J J' : Type v} [Finite J] [Finite J']
  {M N M' N' : Type w} [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup M'] [AddCommGroup N']
  {P : RootDatum J M N} {Q : RootDatum J' M' N'}
  (b : P.Base) (c : Q.Base)

/-- Positive-root transport between two supplied root data preserves their
simple roots. -/
theorem mem_support_equiv_iff_of_positive
    (e : RootPairing.Equiv Q P)
    (hpos : ∀ a, b.IsPos (e.indexEquiv a) ↔ c.IsPos a) (a : J') :
    e.indexEquiv a ∈ b.support ↔ a ∈ c.support := by
  have hf : ∀ a, e.weightEquiv (Q.root a) = P.root (e.indexEquiv a) :=
    fun a => congr_fun e.root_weightMap a
  rw [mem_support_iff_positive_indecomposable P b,
    mem_support_iff_positive_indecomposable Q c, hpos]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro j l hj hl heq
    apply h (e.indexEquiv j) (e.indexEquiv l) ((hpos j).mpr hj) ((hpos l).mpr hl)
    rw [← hf, ← hf, ← hf, heq, map_add]
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro j l hj hl heq
    apply h (e.indexEquiv.symm j) (e.indexEquiv.symm l)
      ((hpos (e.indexEquiv.symm j)).mp (by simpa using hj))
      ((hpos (e.indexEquiv.symm l)).mp (by simpa using hl))
    apply e.weightEquiv.injective
    rw [map_add, hf, hf, hf]
    simpa using heq

end RootPairing.Base

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
  {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ H}
  (hi : IsMaximalTorus i) (hj : IsMaximalTorus j)
  {J J' : Type u} [Finite J] [Finite J']
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}
  (b : P.Base) (c : Q.Base)

omit [Finite J] [Finite J'] in
/-- The root-datum equivalence induced by the actual group and torus maps
preserves positivity when the regular dynamic parabolics agree. -/
theorem positive_iff_of_torusCompatibleIso
    (f : G ≅ H) (t : T ≅ T')
    (hsq : i ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ j)
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hQ : haveI := hH.isAffineHom; IsRootDatumOf j Q)
    (ν : cocharacterLattice T) (ν' : cocharacterLattice T')
    (hν : haveI := hG.isAffineHom; IsRegularCocharacter i ν)
    (hν' : haveI := hH.isAffineHom; IsRegularCocharacter j ν')
    (hb : ∀ a, b.IsPos a ↔ 0 < latticePairing T (P.root a) ν)
    (hc : ∀ a, c.IsPos a ↔ 0 < latticePairing T' (Q.root a) ν')
    (hpar : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).comap f.inv =
      Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ j)) :
    ∀ a, b.IsPos ((rootDatumEquivOfTorusCompatibleIso
      hG hH hT hT' hi hj f t hsq hP hQ).indexEquiv a) ↔ c.IsPos a := by
  let := hG.isAffineHom
  let := hH.isAffineHom
  let e := rootDatumEquivOfTorusCompatibleIso hG hH hT hT' hi hj f t hsq hP hQ
  have hw : ∀ χ, e.weightMap χ = t.hom ≫ χ :=
    rootDatumEquivOfTorusCompatibleIso_weightMap hG hH hT hT' hi hj f t hsq hP hQ
  have hr : ∀ a, P.root (e.indexEquiv a) = t.hom ≫ Q.root a :=
    fun a => (congr_fun e.root_weightMap a).symm.trans (hw (Q.root a))
  have hpair : ∀ χ, latticePairing T' χ (ν ≫ t.hom) =
      latticePairing T (t.hom ≫ χ) ν := by
    intro χ
    simp only [latticePairing_apply, Category.assoc]
  have hνt : IsRegularCocharacter j (ν ≫ t.hom) := by
    intro α hα
    obtain ⟨a, rfl⟩ := hQ.2.1.symm ▸ hα
    rw [hpair, ← hr]
    exact hν _ (hP.2.1 ▸ Set.mem_range_self (e.indexEquiv a))
  have hχ : CommGroupScheme.groupHom (ν ≫ t.hom) ≫ j =
      (CommGroupScheme.groupHom ν ≫ i) ≫ f.hom := by
    change (CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom t.hom) ≫ j = _
    rw [Category.assoc, ← hsq, ← Category.assoc]
  have htransport : Dynamic.parabolic (CommGroupScheme.groupHom (ν ≫ t.hom) ≫ j) =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).comap f.inv := by
    have h := Dynamic.parabolic_eq_comap_of_iso
      (CommGroupScheme.groupHom (ν ≫ t.hom) ≫ j) f.symm
    rw [Iso.symm_hom, hχ] at h
    simpa only [hχ, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  have hsign := ((regularCocharacterBorel k H hH T' j hT' hj).2.1
    (ν ≫ t.hom) ν' hνt hν').mp (htransport.trans hpar)
  intro a
  rw [hb, hc, hr]
  exact (hpair (Q.root a) ▸ hsign (Q.root a) (hQ.2.1 ▸ Set.mem_range_self a))

/-- The actual contravariant root-datum comparison preserves the simple roots
of the two sign-adapted Borel chambers. -/
theorem simple_iff_of_torusCompatibleIso
    (f : G ≅ H) (t : T ≅ T')
    (hsq : i ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ j)
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hQ : haveI := hH.isAffineHom; IsRootDatumOf j Q)
    (ν : cocharacterLattice T) (ν' : cocharacterLattice T')
    (hν : haveI := hG.isAffineHom; IsRegularCocharacter i ν)
    (hν' : haveI := hH.isAffineHom; IsRegularCocharacter j ν')
    (hb : ∀ a, b.IsPos a ↔ 0 < latticePairing T (P.root a) ν)
    (hc : ∀ a, c.IsPos a ↔ 0 < latticePairing T' (Q.root a) ν')
    (hpar : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).comap f.inv =
      Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ j)) :
    ∀ a, (rootDatumEquivOfTorusCompatibleIso
      hG hH hT hT' hi hj f t hsq hP hQ).indexEquiv a ∈ b.support ↔ a ∈ c.support := by
  exact b.mem_support_equiv_iff_of_positive c
    (rootDatumEquivOfTorusCompatibleIso hG hH hT hT' hi hj f t hsq hP hQ)
    (positive_iff_of_torusCompatibleIso hG hH hT hT' hi hj b c
      f t hsq hP hQ ν ν' hν hν' hb hc hpar)

/-- An actual torus-induced comparison together with its Borel chamber and
simple-root compatibility. -/
structure BorelCompatibleRootDatumComparison (t : T ≅ T') where
  rootEquiv : RootPairing.Equiv Q P
  positive_iff : ∀ a, b.IsPos (rootEquiv.indexEquiv a) ↔ c.IsPos a
  simple_iff : ∀ a, rootEquiv.indexEquiv a ∈ b.support ↔ a ∈ c.support
  characters : ∀ χ, rootEquiv.weightMap χ = t.hom ≫ χ
  cocharacters : ∀ μ, rootEquiv.coweightMap μ = μ ≫ t.hom

/-- Construct the Borel-compatible comparison from actual group and torus
isomorphisms and equality of the regular dynamic parabolics. -/
def borelCompatibleRootDatumComparison
    (f : G ≅ H) (t : T ≅ T')
    (hsq : i ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ j)
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hQ : haveI := hH.isAffineHom; IsRootDatumOf j Q)
    (ν : cocharacterLattice T) (ν' : cocharacterLattice T')
    (hν : haveI := hG.isAffineHom; IsRegularCocharacter i ν)
    (hν' : haveI := hH.isAffineHom; IsRegularCocharacter j ν')
    (hb : ∀ a, b.IsPos a ↔ 0 < latticePairing T (P.root a) ν)
    (hc : ∀ a, c.IsPos a ↔ 0 < latticePairing T' (Q.root a) ν')
    (hpar : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).comap f.inv =
      Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ j)) : BorelCompatibleRootDatumComparison b c t where
  rootEquiv := rootDatumEquivOfTorusCompatibleIso hG hH hT hT' hi hj f t hsq hP hQ
  positive_iff := positive_iff_of_torusCompatibleIso hG hH hT hT' hi hj b c
    f t hsq hP hQ ν ν' hν hν' hb hc hpar
  simple_iff := simple_iff_of_torusCompatibleIso hG hH hT hT' hi hj b c
    f t hsq hP hQ ν ν' hν hν' hb hc hpar
  characters := rootDatumEquivOfTorusCompatibleIso_weightMap hG hH hT hT' hi hj
    f t hsq hP hQ
  cocharacters := rootDatumEquivOfTorusCompatibleIso_coweightMap hG hH hT hT' hi hj
    f t hsq hP hQ

end Field

end Langlands.GroupScheme
