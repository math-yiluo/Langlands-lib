import Langlands.GroupScheme.Rational.TorusCentralizerFiniteGaloisModel
import Langlands.GroupScheme.Reductive.RootDatumStatement

/-! # Actual root data on the retained finite-Galois centralizer model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    {A Q : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ G} {j : M ⟶ G}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]

local instance rootDataBaseChangeAffine
    {E : Type u} [Field E]
    (b : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of k))
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom :=
  MorphismProperty.baseChange_obj (P := @IsAffineHom) b H.X inferInstance

/-- Finite reduced actual ambient and centralizer root data on precisely the
torus and field retained by the supplied finite-Galois model. -/
structure TorusCentralizerRootData (C : TorusCentralizerFiniteGaloisModel a j Q) where
  ambientIndex : Type u
  [ambientFinite : Finite ambientIndex]
  ambientDatum : RootDatum ambientIndex
    (characterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap k C.splitting.carrier)).obj C.rational.torus))
    (cocharacterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap k C.splitting.carrier)).obj C.rational.torus))
  ambient_isRootDatum : IsRootDatumOf
    (T := (CommGroupScheme.baseChange
      (algebraBaseMap k C.splitting.carrier)).obj C.rational.torus)
    ((GroupScheme.baseChange (algebraBaseMap k C.splitting.carrier)).map
      (C.rational.centralizer ≫ j)) ambientDatum
  [ambientReduced : ambientDatum.IsReduced]
  centralizerIndex : Type u
  [centralizerFinite : Finite centralizerIndex]
  centralizerDatum : RootDatum centralizerIndex
    (characterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap k C.splitting.carrier)).obj C.rational.torus))
    (cocharacterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap k C.splitting.carrier)).obj C.rational.torus))
  centralizer_isRootDatum : IsRootDatumOf
    (T := (CommGroupScheme.baseChange
      (algebraBaseMap k C.splitting.carrier)).obj C.rational.torus)
    ((GroupScheme.baseChange (algebraBaseMap k C.splitting.carrier)).map
      C.rational.centralizer) centralizerDatum
  [centralizerReduced : centralizerDatum.IsReduced]

attribute [instance] TorusCentralizerRootData.ambientFinite
  TorusCentralizerRootData.centralizerFinite TorusCentralizerRootData.ambientReduced
  TorusCentralizerRootData.centralizerReduced

namespace TorusCentralizerFiniteGaloisModel

variable (C : TorusCentralizerFiniteGaloisModel a j Q)

/-- Apply the supplied root-datum existence proposition to both actual groups
over the same chosen field, without changing the retained torus. -/
def rootData (hroot : RootDatumExistenceStatement.{u})
    (hG : IsConnectedReductive G) (hM : IsConnectedReductive M) :
    TorusCentralizerRootData C := by
  apply Classical.choice
  obtain ⟨J, hJ, P, hP, hPred⟩ :=
    hroot C.splitting.carrier _ (C.ambient_connectedReductive hG) _
      C.splitting.split_left _ C.composite_maximal
  obtain ⟨K, hK, R, hR, hRred⟩ :=
    hroot C.splitting.carrier _ (C.centralizer_connectedReductive hM) _
      C.splitting.split_left _ C.centralizer_maximal
  exact ⟨{
    ambientIndex := J
    ambientFinite := hJ
    ambientDatum := P
    ambient_isRootDatum := hP
    ambientReduced := hPred
    centralizerIndex := K
    centralizerFinite := hK
    centralizerDatum := R
    centralizer_isRootDatum := hR
    centralizerReduced := hRred }⟩

variable [LocallyOfFiniteType G.X.hom]

/-- The canonical base change of the original-field separating cocharacter. -/
def separatingCocharacter (hA : IsSplitTorus A.toGrp) :
    cocharacterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap k C.splitting.carrier)).obj C.rational.torus) :=
  cocharacterLattice.baseChange (algebraBaseMap k C.splitting.carrier)
    C.rational.torus (C.rational.cocharacter hA)

omit [IsAffineHom M.X.hom] in
/-- Ordinary Galois fixedness uses the original-field cocharacter, with no
new cocharacter choice over the splitting field. -/
theorem separatingCocharacter_galois (hA : IsSplitTorus A.toGrp)
    (σ : C.splitting.carrier ≃ₐ[k] C.splitting.carrier) :
    cocharacterLattice.galoisRepresentation k C.splitting.carrier C.rational.torus σ
        (C.separatingCocharacter hA) = C.separatingCocharacter hA :=
  C.rational.cocharacter_baseChange_galois C.splitting.carrier hA σ

end TorusCentralizerFiniteGaloisModel

namespace TorusCentralizerRootData

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom]
    {C : TorusCentralizerFiniteGaloisModel a j Q} (R : TorusCentralizerRootData C)

/-- The roots of the actual centralizer datum are exactly the ambient roots
annihilating the canonical base change of the original separating cocharacter. -/
theorem centralizer_root_range (hA : IsSplitTorus A.toGrp)
    (hj : (torusCentralizer a).IsRepresentedBy j) :
    Set.range R.centralizerDatum.root =
      {χ | χ ∈ Set.range R.ambientDatum.root ∧
        R.ambientDatum.toLinearMap χ (C.separatingCocharacter hA) = 0} := by
  have hroots := C.rational.relativeRoots_baseChange_eq_pairing
    (algebraBaseMap k C.splitting.carrier) hA hj
  rw [← C.rational.centralizer_comp] at hroots
  simpa only [relativeRoots_eq_roots, ← R.centralizer_isRootDatum.2.1,
    ← R.ambient_isRootDatum.2.1, R.ambient_isRootDatum.1,
    TorusCentralizerFiniteGaloisModel.separatingCocharacter] using hroots

/-- The index selection for later cocenter comparison is the zero evaluation
of the same actual ambient root datum on the same retained cocharacter. -/
theorem ambient_root_mem_centralizer_iff (hA : IsSplitTorus A.toGrp)
    (hj : (torusCentralizer a).IsRepresentedBy j) (p : R.ambientIndex) :
    R.ambientDatum.root p ∈ Set.range R.centralizerDatum.root ↔
      R.ambientDatum.root' p (C.separatingCocharacter hA) = 0 := by
  rw [R.centralizer_root_range hA hj]
  simp only [Set.mem_ofPred_eq, Set.mem_range_self, true_and]

end TorusCentralizerRootData

end Langlands.GroupScheme
