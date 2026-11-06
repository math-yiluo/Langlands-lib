import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Root-data comparison from an actual geometric group isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section TorusCompatible

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
  {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ H}
  (hi : IsMaximalTorus i) (hj : IsMaximalTorus j)
  {J J' : Type u}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}

include hT hT' hi hj

/-- A group isomorphism compatible with a torus isomorphism gives a full
contravariant equivalence of the supplied actual root data. -/
theorem exists_rootDatumEquiv_of_torusCompatibleIso
    (f : G ≅ H) (t : T ≅ T')
    (hsq : i ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ j)
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hQ : haveI := hH.isAffineHom; IsRootDatumOf j Q) :
    ∃ e : RootPairing.Equiv Q P,
      (∀ χ, e.weightMap χ = t.hom ≫ χ) ∧
      (∀ ν, e.coweightMap ν = ν ≫ t.hom) := by
  obtain ⟨a, ha, hb, -, -, hiso⟩ :=
    centralIsogenyRootDatumHom k G H hG hH T T' hT hT' i j hi hj
      f.hom t.hom (isCentralIsogeny_of_isIso f.hom) hsq J J' P Q hP hQ
  have hw : Function.Bijective a.weightMap := hiso.mp inferInstance
  have hc : Function.Bijective a.coweightMap := by
    have heq : a.coweightMap =
        (cocharacterLattice.congr t).toIntLinearEquiv.toLinearMap := by
      ext ν
      exact hb ν
    rw [heq]
    exact (cocharacterLattice.congr t).bijective
  exact ⟨{ a with bijective_weightMap := hw, bijective_coweightMap := hc }, ha, hb⟩

/-- The full contravariant root-datum equivalence induced by a torus-compatible
group isomorphism. -/
def rootDatumEquivOfTorusCompatibleIso
    (f : G ≅ H) (t : T ≅ T')
    (hsq : i ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ j)
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hQ : haveI := hH.isAffineHom; IsRootDatumOf j Q) :
    RootPairing.Equiv Q P :=
  Classical.choose
    (exists_rootDatumEquiv_of_torusCompatibleIso hG hH hT hT' hi hj f t hsq hP hQ)

theorem rootDatumEquivOfTorusCompatibleIso_weightMap
    (f : G ≅ H) (t : T ≅ T')
    (hsq : i ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ j)
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hQ : haveI := hH.isAffineHom; IsRootDatumOf j Q)
    (χ : characterLattice T') :
    (rootDatumEquivOfTorusCompatibleIso hG hH hT hT' hi hj f t hsq hP hQ).weightMap χ =
      t.hom ≫ χ :=
  (Classical.choose_spec
    (exists_rootDatumEquiv_of_torusCompatibleIso hG hH hT hT' hi hj f t hsq hP hQ)).1 χ

theorem rootDatumEquivOfTorusCompatibleIso_coweightMap
    (f : G ≅ H) (t : T ≅ T')
    (hsq : i ≫ f.hom = CommGroupScheme.groupHom t.hom ≫ j)
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hQ : haveI := hH.isAffineHom; IsRootDatumOf j Q)
    (ν : cocharacterLattice T) :
    (rootDatumEquivOfTorusCompatibleIso hG hH hT hT' hi hj f t hsq hP hQ).coweightMap ν =
      ν ≫ t.hom :=
  (Classical.choose_spec
    (exists_rootDatumEquiv_of_torusCompatibleIso hG hH hT hT' hi hj f t hsq hP hQ)).2 ν

/-- Over an algebraically closed field, the root data on any two chosen split
maximal tori of isomorphic connected reductive groups are equivalent. -/
theorem nonempty_rootDatumEquiv_of_iso_of_isAlgClosed [IsAlgClosed k]
    (f : G ≅ H)
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hQ : haveI := hH.isAffineHom; IsRootDatumOf j Q) :
    Nonempty (RootPairing.Equiv P Q) := by
  let := hH.smooth
  let := hH.isAffineHom
  let := hH.connectedSpace
  obtain ⟨g, t, ht⟩ := maximalTorusConjugacy k H T T' (i ≫ f.hom) j
    (hi.comp_iso f) hj
  obtain ⟨e, -, -⟩ := exists_rootDatumEquiv_of_torusCompatibleIso hG hH hT hT' hi hj
    (f ≪≫ H.innerIso g) t (by simpa only [Iso.trans_hom, Category.assoc] using ht) hP hQ
  exact ⟨e.symm⟩

end TorusCompatible

end Langlands.GroupScheme
