import Langlands.GroupScheme.Reductive.RelativeIsogenyConjugationRigidity
import Langlands.GroupScheme.Reductive.NormalizedLocalRootFamily
import Langlands.GroupScheme.Reductive.LocalRootParametrizationRigidity

/-! # Simple-root rigidity checked over local coefficient algebras -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace Langlands.GroupScheme

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
  [Finite J] [Finite J']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)} [P.IsReduced] [Q.IsReduced]
  {p : ℕ}

namespace RelativeIsogeny

/-- Over a local ring, actual simple-root parametrizations determine finite
homomorphisms with a common root-datum map, without a supplied Weyl normalization. -/
theorem hom_ext_of_simpleRootParametrizations [IsLocalRing R]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hQ : IsFibrewiseRootDatumOf I' H j Q)
    (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
      splitTorus.exponentCharacter _ I (r.weightMap m))
    (phi Phi : G ⟶ H) [IsFinite phi.hom.hom.left] [IsFinite Phi.hom.hom.left]
    (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
    (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j)
    (hG : IsReductive G) (hH : IsReductive H)
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hmaxG : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
    (b : P.Base) (u : J → (Ga R ⟶ G))
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (he : ∀ a ∈ b.support, u a ≫ phi = u a ≫ Phi) : phi = Phi := by
  classical
  obtain ⟨w, hw, hn⟩ := exists_normalizedLocalRootFamily hG i hi hmaxG hP b
  choose v hv using fun a : J' =>
    LocalRootGroup.exists_rootParametrization_of_flat j hH hmaxH hQ a
  apply hom_ext_of_simpleRootRestrictions i j hP hQ r tau hweight phi hphi hH hmaxH
    Phi hPhi hG hi hj hmaxG b w v
    (fun a _ => ⟨hw a, hw (P.reflectionPerm a a)⟩)
    (fun a _ => ⟨hv (r.indexEquiv.symm a),
      hv (Q.reflectionPerm (r.indexEquiv.symm a) (r.indexEquiv.symm a))⟩) hn
  intro a ha
  obtain ⟨c, hc, _⟩ := (hw a).existsUnique_unit_of_rootDatum hP a (hu a ha)
  rw [hc, Category.assoc, Category.assoc, he a ha]

end RelativeIsogeny

/-- Local-ring finite homomorphisms with a common root-datum map are
determined by any supplied actual simple-root parametrizations. -/
def SimpleRootLocalTestRigidityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (I I' J J' : Type u) [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
    [Finite J] [Finite J']
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (Q : RootDatum J' (I' → ℤ) (I' → ℤ)) [P.IsReduced] [Q.IsReduced]
    (p : ℕ) (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H),
    IsFibrewiseRootDatumOf I G i P → IsFibrewiseRootDatumOf I' H j Q →
    ∀ (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
      (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
        splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I'),
    (∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
      splitTorus.exponentCharacter _ I (r.weightMap m)) →
    ∀ (phi Phi : G ⟶ H) [IsFinite phi.hom.hom.left] [IsFinite Phi.hom.hom.left],
    i ≫ phi = CommGroupScheme.groupHom tau ≫ j →
    i ≫ Phi = CommGroupScheme.groupHom tau ≫ j →
    IsReductive G → IsReductive H → IsClosedSubgroup i → IsClosedSubgroup j →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j →
    ∀ (b : P.Base) (u : J → (Ga R ⟶ G)),
    (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a)) →
    (∀ a ∈ b.support, u a ≫ phi = u a ≫ Phi) → phi = Phi

/-- The local test criterion follows from normalized local families and unit
comparison of actual parametrizations. -/
theorem simpleRootLocalTestRigidity : SimpleRootLocalTestRigidityStatement.{u} := by
  intro R _ _ I I' J J' _ _ _ _ _ _ G H _ _ P Q _ _ p i j hP hQ r tau
    hweight phi Phi _ _ hphi hPhi hG hH hi hj hmaxG hmaxH b u hu he
  exact RelativeIsogeny.hom_ext_of_simpleRootParametrizations i j hP hQ r tau hweight
    phi Phi hphi hPhi hG hH hi hj hmaxG hmaxH b u hu he

section Conjugation

attribute [local irreducible] torusConjugateAlgebraHom

variable {V : Over (Spec (CommRingCat.of R))}

/-- Simple-root conjugation on all refinements determines whole-group
conjugation over an arbitrary ring. Normalized families are needed only on
local test algebras, where they are constructed internally. -/
theorem TorusConjugates.of_simpleRootParametrizations
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hQ : IsFibrewiseRootDatumOf I' H j Q)
    (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
    (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
      splitTorus.exponentCharacter _ I (r.weightMap m))
    (phi Phi : G ⟶ H) [hfinphi : IsFinite phi.hom.hom.left] [hfinPhi : IsFinite Phi.hom.hom.left]
    (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
    (hPhi : i ≫ Phi = CommGroupScheme.groupHom tau ≫ j)
    (hG : IsReductive G) (hH : IsReductive H)
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hmaxG : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
    (b : P.Base) (u : J → (Ga R ⟶ G))
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (t : V ⟶ (splitTorus.commGroupScheme _ I').X)
    (he : ∀ a ∈ b.support, TorusConjugatesOnRoot j phi Phi t (u a)) :
    TorusConjugates j phi Phi t := by
  classical
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : Smooth H.X.hom := hH.smooth
  apply TorusConjugates.of_localAlgebraHom j phi Phi t
  intro A _ _ _ a
  have heA (α : J) (hα : α ∈ b.support) :
      baseChangeRoot A (u α) ≫ (baseChange (algebraBaseMap R A)).map phi =
        baseChangeRoot A (u α) ≫ torusConjugateAlgebraHom A j Phi t a :=
    torusConjugateAlgebraHom_root (R := R) (G := G) (H := H)
      (T := splitTorus.commGroupScheme _ I') (V := V)
      j phi Phi t (u α) (he α hα) A a
  have hPA := hP.baseChange_implicit (A := A)
  have hQA := hQ.baseChange_implicit (A := A)
  have hGA := hG.baseChange (algebraBaseMap R A)
  have hHA := hH.baseChange (algebraBaseMap R A)
  have hmaxGA := splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmaxG (A := A)
  have hmaxHA := splitTorus.isFibrewiseMaximalTorus_baseChangeHom I' H j hmaxH (A := A)
  let hGAff : IsAffineHom ((baseChange (algebraBaseMap R A)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))
  let hHAff : IsAffineHom ((baseChange (algebraBaseMap R A)).obj H).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom (algebraBaseMap R A)))
  let hfinphiA : IsFinite ((baseChange (algebraBaseMap R A)).map phi).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (baseChange_map_isPullback (algebraBaseMap R A) phi).flip inferInstance
  let hfinconjA : IsFinite (torusConjugateAlgebraHom A j Phi t a).hom.hom.left :=
    isFinite_torusConjugateAlgebraHom (hFfinite := hfinPhi) A j Phi t a
  refine @RelativeIsogeny.hom_ext_of_simpleRootParametrizations
    A _ I I' J J' _ _ _ _ _ _
    ((baseChange (algebraBaseMap R A)).obj G) ((baseChange (algebraBaseMap R A)).obj H)
    hGAff hHAff P Q _ _ p _
    (splitTorus.baseChangeHom (K := A) G I i)
    (splitTorus.baseChangeHom (K := A) H I' j)
    hPA hQA r (splitTorus.coordinateBaseChangeHom (algebraBaseMap R A) tau) ?_
    ((baseChange (algebraBaseMap R A)).map phi) (torusConjugateAlgebraHom A j Phi t a)
    hfinphiA hfinconjA ?_ ?_ hGA hHA ?_ ?_ hmaxGA hmaxHA
    b (fun α => baseChangeRoot A (u α)) ?_ ?_
  · exact splitTorus.coordinateBaseChangeHom_character (algebraBaseMap R A) tau r.weightMap hweight
  · exact splitTorus.coordinateBaseChangeHom_square A i j tau phi hphi
  · exact (torusConjugateAlgebraHom_torus j Phi t i (CommGroupScheme.groupHom tau) hPhi A a).trans
      (splitTorus.coordinateBaseChangeHom_square A i j tau Phi hPhi)
  · exact (IsClosedSubgroup.of_iso (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm).comp
      (hi.baseChange (algebraBaseMap R A))
  · exact (IsClosedSubgroup.of_iso (splitTorus.baseChangeIso (algebraBaseMap R A) I').symm).comp
      (hj.baseChange (algebraBaseMap R A))
  · exact fun α hα => isRootParametrization_baseChangeRoot A i _ _ (hu α hα)
  · exact heA

end Conjugation

end Langlands.GroupScheme
