import Langlands.GroupScheme.Reductive.RootFactorCellBaseChange
import Langlands.GroupScheme.Reductive.SplitDataBaseChange

/-! # Openness of actual factor cells from field coordinates -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootFactorCell

open LocalSplitCell RelativeRoot

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
    {m n : ℕ} (A : Fin m → GroupScheme (Spec (CommRingCat.of R)))
    (D : GroupScheme (Spec (CommRingCat.of R)))
    (B : Fin n → GroupScheme (Spec (CommRingCat.of R)))

/-- Chosen additive factor coordinates and torus coordinates identify the
standard cell source with the actual factor source. -/
def vectorSourceIso
    (eA : ∀ i, Ga R ≅ A i) (eD : splitTorus (Spec (CommRingCat.of R)) I ≅ D)
    (eB : ∀ i, Ga R ≅ B i) :
    cellObj R I m n ≅ (sourceGroup A D B).X :=
  tensorIso
    (tensorIso ((Grp.forget _).mapIso (vectorProductIso (CommRingCat.of R) m A eA))
      ((Grp.forget _).mapIso eD))
    ((Grp.forget _).mapIso (vectorProductIso (CommRingCat.of R) n B eB))

variable {G : GroupScheme (Spec (CommRingCat.of R))} {J : Type u}

/-- An actual ordered product in chosen additive factor coordinates is the
published ordered root-point formula, with every factor map retained. -/
theorem vectorProductIso_ordered (jA : ∀ i, A i ⟶ G) (eA : ∀ i, Ga R ≅ A i)
    (fam : J → (Ga R ⟶ G)) (neg : Fin m → J)
    (hA : ∀ i, (eA i).hom ≫ jA i = fam (neg i))
    (Z : Over (Spec (CommRingCat.of R)))
    (x : Z ⟶ (VectorGroup.groupScheme (CommRingCat.of R) m).X) :
    (x ≫ (vectorProductIso (CommRingCat.of R) m A eA).hom.hom.hom) ≫
        orderedMultiplication jA =
      orderedProduct fam neg Z (VectorGroup.coordinates (CommRingCat.of R) m Z x).toAdd := by
  rw [comp_orderedMultiplication, orderedPoints, orderedProduct]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp only [finiteProductPointsEquiv_apply]
  calc
    _ = (x ≫ (vectorProductIso (CommRingCat.of R) m A eA).hom.hom.hom ≫
          (Pi.π A i).hom.hom) ≫ (jA i).hom.hom := by simp only [Category.assoc]
    _ = (VectorGroup.scalarPoint (CommRingCat.of R) Z
          ((VectorGroup.coordinates (CommRingCat.of R) m Z x).toAdd i) ≫
            (eA i).hom.hom.hom) ≫ (jA i).hom.hom :=
      congrArg (fun p => p ≫ (jA i).hom.hom)
        (vectorProductIso_hom_π (CommRingCat.of R) m A eA Z x i)
    _ = _ := by rw [Category.assoc, ← Grp.comp_hom_hom, hA]; rfl

end Langlands.GroupScheme.RootFactorCell

namespace Langlands.GroupScheme.RootFactorCell

open LocalSplitCell RelativeRoot

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
    {m n : ℕ} (A : Fin m → GroupScheme (Spec (CommRingCat.of R)))
    (D : GroupScheme (Spec (CommRingCat.of R)))
    (B : Fin n → GroupScheme (Spec (CommRingCat.of R)))
    {G : GroupScheme (Spec (CommRingCat.of R))} {J : Type u}

/-- The source comparison identifies actual factor multiplication with the
standard cell map whenever it matches every supplied factor. -/
theorem vectorSourceIso_hom_multiplication
    (eA : ∀ i, Ga R ≅ A i) (eD : splitTorus (Spec (CommRingCat.of R)) I ≅ D)
    (eB : ∀ i, Ga R ≅ B i) (jA : ∀ i, A i ⟶ G) (jD : D ⟶ G) (jB : ∀ i, B i ⟶ G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (fam : J → (Ga R ⟶ G))
    (neg : Fin m → J) (pos : Fin n → J)
    (hA : ∀ r, (eA r).hom ≫ jA r = fam (neg r))
    (hD : eD.hom ≫ jD = i) (hB : ∀ r, (eB r).hom ≫ jB r = fam (pos r)) :
    (vectorSourceIso A D B eA eD eB).hom ≫ multiplication A D B jA jD jB =
      cellMap i fam neg pos := by
  have hneg : (vectorSourceIso A D B eA eD eB).hom ≫
      fst _ _ ≫ fst _ _ ≫ orderedMultiplication jA =
      orderedProduct fam neg _ (negCoord (𝟙 (cellObj R I m n))) := by
    simp only [vectorSourceIso, tensorIso_hom, Functor.mapIso_hom,
      tensorHom_fst_assoc]
    change (fst _ _ ≫ fst _ _) ≫ (vectorProductIso (CommRingCat.of R) m A eA).hom.hom.hom ≫
      orderedMultiplication jA = _
    have h := vectorProductIso_ordered A jA eA fam neg hA
      (cellObj R I m n) (fst _ _ ≫ fst _ _)
    simpa only [negCoord, Category.id_comp, Category.assoc] using h
  have hmid : (vectorSourceIso A D B eA eD eB).hom ≫
      fst _ _ ≫ snd _ _ ≫ jD.hom.hom = torusCoord (𝟙 (cellObj R I m n)) ≫ i.hom.hom := by
    simp only [vectorSourceIso, tensorIso_hom, Functor.mapIso_hom,
      tensorHom_fst_assoc, tensorHom_snd_assoc]
    change fst _ _ ≫ snd _ _ ≫ eD.hom.hom.hom ≫ jD.hom.hom = _
    rw [← Grp.comp_hom_hom, hD]
    rfl
  have hpos : (vectorSourceIso A D B eA eD eB).hom ≫
      snd _ _ ≫ orderedMultiplication jB =
      orderedProduct fam pos _ (posCoord (𝟙 (cellObj R I m n))) := by
    simp only [vectorSourceIso, tensorIso_hom, Functor.mapIso_hom,
      tensorHom_snd_assoc]
    change snd _ _ ≫ (vectorProductIso (CommRingCat.of R) n B eB).hom.hom.hom ≫
      orderedMultiplication jB = _
    have h := vectorProductIso_ordered B jB eB fam pos hB
      (cellObj R I m n) (snd _ _)
    simpa only [posCoord, Category.id_comp, Category.assoc] using h
  simp only [multiplication, MonObj.comp_mul, cellMap, cellPoint]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) hneg hmid) hpos

end Langlands.GroupScheme.RootFactorCell

namespace Langlands.GroupScheme.RootFactorCell

open LocalSplitCell RelativeRoot

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
    {m n : ℕ} {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Smooth actual root factors give an open cell when their supplied
field-fibre additive coordinates are the prescribed root parametrizations. -/
theorem isOpenImmersion_multiplication_of_fieldCoordinates
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (bs : P.Base)
    (neg : Fin m ≃ {a // ¬ bs.IsPos a}) (pos : Fin n ≃ {a // bs.IsPos a})
    (A : Fin m → GroupScheme (Spec (CommRingCat.of R)))
    (B : Fin n → GroupScheme (Spec (CommRingCat.of R)))
    (jA : ∀ r, A r ⟶ G) (jB : ∀ r, B r ⟶ G)
    (hA : ∀ r, Smooth (A r).X.hom) (hB : ∀ r, Smooth (B r).X.hom)
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K],
      ∃ (fam : J → (Ga K ⟶ (GroupScheme.baseChange (algebraBaseMap R K)).obj G))
        (eA : ∀ r, Ga K ≅ (GroupScheme.baseChange (algebraBaseMap R K)).obj (A r))
        (eB : ∀ r, Ga K ≅ (GroupScheme.baseChange (algebraBaseMap R K)).obj (B r)),
        (∀ a, IsRootParametrization (splitTorus.baseChangeHom (K := K) G I i)
          (P.root a) (fam a)) ∧
        (∀ r, (eA r).hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jA r) =
          fam (neg r : J)) ∧
        (∀ r, (eB r).hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jB r) =
          fam (pos r : J))) :
    IsOpenImmersion (multiplication A (splitTorus (Spec (CommRingCat.of R)) I) B jA i jB).left := by
  have : Smooth G.X.hom := hG.smooth
  have : Smooth (sourceGroup A (splitTorus (Spec (CommRingCat.of R)) I) B).X.hom :=
    smooth_sourceGroup A _ B hA (smooth_splitTorus I) hB
  apply Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise
    (multiplication A (splitTorus (Spec (CommRingCat.of R)) I) B jA i jB)
  intro s
  let K := (Spec (CommRingCat.of R)).residueField s
  let : Algebra R K :=
    (Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)).hom.toAlgebra
  have hb : algebraBaseMap R K = (Spec (CommRingCat.of R)).fromSpecResidueField s :=
    Spec.map_preimage _
  let b := algebraBaseMap R K
  let GK := (GroupScheme.baseChange b).obj G
  let AK := fun r => (GroupScheme.baseChange b).obj (A r)
  let BK := fun r => (GroupScheme.baseChange b).obj (B r)
  let DK := (GroupScheme.baseChange b).obj (splitTorus (Spec (CommRingCat.of R)) I)
  let jAK := fun r => (GroupScheme.baseChange b).map (jA r)
  let jBK := fun r => (GroupScheme.baseChange b).map (jB r)
  let jDK := (GroupScheme.baseChange b).map i
  have hGK : IsReductive GK := hG.baseChange b
  have : IsAffineHom GK.X.hom := hGK.isAffineHom
  obtain ⟨fam, eA, eB, hfam, heA, heB⟩ := hfib K
  let eD := (splitTorus.baseChangeIso b I).symm
  let e := vectorSourceIso AK DK BK eA eD eB
  have he : e.hom ≫ multiplication AK DK BK jAK jDK jBK =
      cellMap (splitTorus.baseChangeHom (K := K) G I i) fam
        (fun r => (neg r : J)) (fun r => (pos r : J)) :=
    vectorSourceIso_hom_multiplication AK DK BK eA eD eB jAK jDK jBK
      (splitTorus.baseChangeHom (K := K) G I i) fam _ _ heA rfl heB
  have hopen : IsOpenImmersion (e.hom ≫ multiplication AK DK BK jAK jDK jBK).left := by
    rw [he]
    exact LocalSplitBigCell.isOpenImmersion_cellMap hGK (hmax.baseChange_coordinates b)
      (IsFibrewiseRootDatumOf.baseChange G I i hP) bs fam hfam neg pos
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hmul : IsOpenImmersion (multiplication AK DK BK jAK jDK jBK).left := by
    rw [Over.comp_left] at hopen
    exact (MorphismProperty.cancel_left_of_respectsIso (@IsOpenImmersion)
      e.hom.left (multiplication AK DK BK jAK jDK jBK).left).mp hopen
  have h : IsOpenImmersion ((Over.pullback b).map
      (multiplication A (splitTorus (Spec (CommRingCat.of R)) I) B jA i jB)).left := by
    rw [← multiplication_baseChange]
    have : IsIso (sourceBaseChangeIso b A (splitTorus (Spec (CommRingCat.of R)) I) B).hom.left :=
      (Over.forget (Spec (CommRingCat.of K))).map_isIso
        (sourceBaseChangeIso b A (splitTorus (Spec (CommRingCat.of R)) I) B).hom
    change IsOpenImmersion
      ((sourceBaseChangeIso b A (splitTorus (Spec (CommRingCat.of R)) I) B).hom.left ≫
        (multiplication AK DK BK jAK jDK jBK).left)
    let : IsOpenImmersion (multiplication AK DK BK jAK jDK jBK).left := hmul
    infer_instance
  change IsOpenImmersion ((Over.pullback (algebraBaseMap R K)).map
    (multiplication A (splitTorus (Spec (CommRingCat.of R)) I) B jA i jB)).left at h
  rw [hb] at h
  exact h

end Langlands.GroupScheme.RootFactorCell
