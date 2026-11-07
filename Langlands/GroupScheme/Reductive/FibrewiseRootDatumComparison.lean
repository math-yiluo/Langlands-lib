import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.RootDatumFieldComparison
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Compare common coordinate root data on one field fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R]
  {I I' : Type u} [Fintype I] [Fintype I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
  {J J' : Type u}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}

local instance comparisonFibreAffine {k : Type u} [Field k] [Algebra R k]
    {F : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom F.X.hom] :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj F).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd F.X.hom (algebraBaseMap R k)))

/-- An isomorphism on one actual field fibre determines equivalent full
coordinate data, when the supplied torus maps are maximal on that fibre. -/
theorem IsFibrewiseRootDatumOf.nonempty_equiv_of_fieldIso
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hQ : IsFibrewiseRootDatumOf I' H j Q)
    (k : Type u) [Field k] [Algebra R k]
    (hGk : IsConnectedReductive ((baseChange (algebraBaseMap R k)).obj G))
    (hHk : IsConnectedReductive ((baseChange (algebraBaseMap R k)).obj H))
    (hik : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i))
    (hjk : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I')
      (splitTorus.baseChangeHom (K := k) H I' j))
    (f : (baseChange (algebraBaseMap R k)).obj G ≅
      (baseChange (algebraBaseMap R k)).obj H) :
    Nonempty (RootPairing.Equiv P Q) := by
  obtain ⟨e⟩ := nonempty_rootDatumEquiv_of_iso hGk hHk
    (isSplitTorus_splitTorus I) (isSplitTorus_splitTorus I')
    hik hjk f (hP.field k) (hQ.field k)
  exact ⟨CoordinateRootDatum.equivOfFieldRealizationEquiv k P Q e⟩

/-- Choose the full coordinate equivalence supplied by one field-fibre
isomorphism. The isomorphism need not carry either chosen torus to the other. -/
def IsFibrewiseRootDatumOf.equivOfFieldIso
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hQ : IsFibrewiseRootDatumOf I' H j Q)
    (k : Type u) [Field k] [Algebra R k]
    (hGk : IsConnectedReductive ((baseChange (algebraBaseMap R k)).obj G))
    (hHk : IsConnectedReductive ((baseChange (algebraBaseMap R k)).obj H))
    (hik : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i))
    (hjk : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I')
      (splitTorus.baseChangeHom (K := k) H I' j))
    (f : (baseChange (algebraBaseMap R k)).obj G ≅
      (baseChange (algebraBaseMap R k)).obj H) :
    RootPairing.Equiv P Q :=
  Classical.choice (hP.nonempty_equiv_of_fieldIso hQ k hGk hHk hik hjk f)

/-- Global reductivity supplies the connected reductivity needed on the
chosen field fibre; no local-ring or algebraic-closedness hypothesis is needed. -/
theorem IsFibrewiseRootDatumOf.nonempty_equiv_of_reductive_fieldIso
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hQ : IsFibrewiseRootDatumOf I' H j Q)
    (hG : IsReductive G) (hH : IsReductive H)
    (k : Type u) [Field k] [Algebra R k]
    (hik : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i))
    (hjk : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I')
      (splitTorus.baseChangeHom (K := k) H I' j))
    (f : (baseChange (algebraBaseMap R k)).obj G ≅
      (baseChange (algebraBaseMap R k)).obj H) :
    Nonempty (RootPairing.Equiv P Q) :=
  hP.nonempty_equiv_of_fieldIso hQ k
    (hG.isConnectedReductive_algebraMap k) (hH.isConnectedReductive_algebraMap k)
    hik hjk f

end Langlands.GroupScheme
