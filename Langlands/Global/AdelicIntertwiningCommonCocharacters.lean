import Langlands.Global.AdelicIntertwiningHaarOffset
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Dynamic.EqualCentralizerDeterminantBalance
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer

/-! # Common cocharacters for the radical determinant comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {iU : U ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  {q : Q ⟶ G} {l' : M' ⟶ Q} {iV : V ⟶ Q} {a' : A'.toGrp ⟶ M'}
  (r' : ParabolicRootPresentation q l' a')
  {c : M' ⟶ M} {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  (hw : IsWeylConjugation p l q l' w c)

local notation "χP" => CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p
local notation "χQ" => CommGroupScheme.groupHom r'.splitComponentCocharacter ≫ a' ≫ l' ≫ q

include hw in
/-- In the direction from the source Levi to the target Levi, the ambient image is
conjugation by the Weyl representative. -/
theorem IsWeylConjugation.comp_inner_hom [IsIso c] :
    (l ≫ p) ≫ (G.innerIso w).hom = inv c ≫ l' ≫ q := by
  apply (cancel_epi c).mp
  rw [← Category.assoc c, hw.comp_eq]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, IsIso.hom_inv_id_assoc]

private theorem range_comp_iso_eq_comap {X Y Z : GroupScheme (Spec (CommRingCat.of F))}
    (j : X ⟶ Y) (f : Y ≅ Z) :
    SubgroupFunctor.range (j ≫ f.hom) = (SubgroupFunctor.range j).comap f.inv :=
  SubgroupFunctor.range_eq_comap_of_iso_square f.symm (Iso.refl X) (by simp)

/-- The transported source unipotent is a dynamic unipotent for the conjugated source
cocharacter. -/
theorem range_conjugate_sourceRadical [Smooth G.X.hom] (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) :
    SubgroupFunctor.range (iU ≫ p ≫ (G.innerIso w).hom) = Dynamic.unipotent (χP ≫ (G.innerIso w).hom) := by
  let χ := χP
  have hχ : Dynamic.unipotent (χ ≫ (G.innerIso w).hom) = (Dynamic.unipotent χ).comap (G.innerIso w).inv := by
    rw [Dynamic.unipotent_eq_comap_of_iso (χ ≫ (G.innerIso w).hom) (G.innerIso w).symm]
    simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc iU p, range_comp_iso_eq_comap, r.range_comp_radical_eq hU]
  exact hχ.symm

include hw in
/-- After conjugating the source cocharacter its centralizer is the actual target Levi. -/
theorem centralizer_conjugate_sourceCocharacter :
    Dynamic.centralizer (χP ≫ (G.innerIso w).hom) = SubgroupFunctor.range (l' ≫ q) := by
  let : IsIso c := hw.isIso
  let χ := χP
  have hχ : Dynamic.centralizer (χ ≫ (G.innerIso w).hom) = (Dynamic.centralizer χ).comap (G.innerIso w).inv := by
    rw [Dynamic.centralizer_eq_comap_of_iso (χ ≫ (G.innerIso w).hom) (G.innerIso w).symm]
    simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hχ, ← r.levi_eq_splitComponentCocharacter, ← range_comp_iso_eq_comap,
    hw.comp_inner_hom]
  exact SubgroupFunctor.range_iso_comp (asIso c).symm (l' ≫ q)

variable [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]

include hw in
/-- The target presentation's maximal split torus carries both the conjugate source and the
target cocharacters. The Levi factor of the torus detects every rational Levi character. -/
theorem exists_commonIntertwiningCocharacters :
    ∃ (ζ ξ : cocharacterLattice r'.data.T) (t : r'.data.T.toGrp ⟶ M'),
      CommGroupScheme.groupHom ζ ≫ r'.data.i = χP ≫ (G.innerIso w).hom ∧
      CommGroupScheme.groupHom ξ ≫ r'.data.i = χQ ∧
      t ≫ l' ≫ q = r'.data.i ∧ Function.Injective (characterRestrict t) := by
  let : IsIso c := hw.isIso
  have ha := ((r.isCompatible.splitComponent.comp_iso (asIso c).symm).isCentralSplitTorus :
    IsCentralSplitTorus (a ≫ inv c))
  obtain ⟨f, hf⟩ := r'.isCompatible.splitComponent.exists_comp_eq (finiteType_coordinateAlgebra M') ha
  let ζ := RealTorusSpace.cocharacterMapInt (Additive.ofMul f ≫ r'.data.f) r.splitComponentCocharacter
  let ξ := RealTorusSpace.cocharacterMapInt r'.data.f r'.splitComponentCocharacter
  let j := l' ≫ q
  have : Mono j.hom.hom.left := (r'.isCompatible.levi.isClosedSubgroup.comp r'.isCompatible.parabolic.isClosedSubgroup).mono
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hj : (standardLevi r'.data.i r'.data.ν r'.data.J).IsRepresentedBy j :=
    ⟨inferInstance, r'.isCompatible.levi_eq⟩
  let t := standardLeviTorusFactor r'.data.i r'.data.ν r'.data.J hj
  have ht : t ≫ j = r'.data.i := standardLeviTorusFactor_comp _ _ _ hj
  have hfact : CommGroupScheme.groupHom r'.data.f ≫ t = a' := hj.hom_ext (by
    rw [Category.assoc, ht]
    exact r'.isCompatible.factor_comp)
  refine ⟨ζ, ξ, t, ?_, ?_, ht, ?_⟩
  · change (CommGroupScheme.groupHom r.splitComponentCocharacter ≫
      (f ≫ CommGroupScheme.groupHom r'.data.f)) ≫ r'.data.i = _
    simp only [Category.assoc, r'.isCompatible.factor_comp, ← Category.assoc f a', hf]
    simpa only [Category.assoc, Iso.symm_hom, asIso_inv] using congrArg
      (fun k : M ⟶ G => CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ k)
      hw.comp_inner_hom.symm
  · change (CommGroupScheme.groupHom r'.splitComponentCocharacter ≫
      CommGroupScheme.groupHom r'.data.f) ≫ r'.data.i = _
    rw [Category.assoc, r'.isCompatible.factor_comp]
  · have hdet := characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter
      r'.isCompatible.levi.isConnectedReductive r'.isCompatible.splitComponent
    rw [← hfact, characterRestrict_comp] at hdet
    intro x y hxy
    apply hdet
    exact congrArg (characterRestrict (CommGroupScheme.groupHom r'.data.f)) hxy


variable {C : GroupScheme (Spec (CommRingCat.of F))} {iC : C ⟶ G}
  [IsAffineHom U.X.hom] [IsAffineHom V.X.hom] [IsAffineHom C.X.hom]

include hw in
/-- The product of the two radical determinants is the square of the stabilizer
determinant on the common target Levi. All actions use the actual subgroup representatives. -/
theorem intertwiningRadicalDeterminantBalance (hG : IsConnectedReductive G)
    {dU dV dC : ℕ} (bU : Lie.FiniteCoordinates U dU) (bV : Lie.FiniteCoordinates V dV)
    (bC : Lie.FiniteCoordinates C dC) :
    ∀ (hU : (Dynamic.unipotent (χP ≫ (G.innerIso w).hom)).IsRepresentedBy
        (iU ≫ p ≫ (G.innerIso w).hom))
      (hV : (Dynamic.unipotent χQ).IsRepresentedBy (iV ≫ q))
      (hC : (Dynamic.unipotent (χP ≫ (G.innerIso w).hom) ⊓ Dynamic.unipotent χQ).IsRepresentedBy iC)
      (hZ : SubgroupFunctor.range (l' ≫ q) ≤ Dynamic.centralizer (χP ≫ (G.innerIso w).hom))
      (hZ' : SubgroupFunctor.range (l' ≫ q) ≤ Dynamic.centralizer χQ),
      (Dynamic.centralizingUnipotentAction _ (l' ≫ q) hZ hU).determinantCharacter bU +
        (Dynamic.centralizingUnipotentAction _ (l' ≫ q) hZ' hV).determinantCharacter bV =
      2 • (Dynamic.centralizingUnipotentIntersectionAction _ _ (l' ≫ q) hZ hZ' hC).determinantCharacter bC := by
  let i := r'.data.i
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : Mono i.hom.hom.left := r'.isCompatible.maximalSplit.isSplitSubtorus.mono
  have hroot : HasRelativeRootSystem i := relativeRootSystem F G hG r'.data.T i r'.isCompatible.maximalSplit
  obtain ⟨ζ, ξ, t, hζ, hξ, ht, hdetect⟩ := exists_commonIntertwiningCocharacters r r' hw
  have hEq : Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) =
      Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ i) := by
    change Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ r'.data.i) = _
    rw [hζ, hξ, centralizer_conjugate_sourceCocharacter r hw, r'.levi_eq_splitComponentCocharacter]
  rw [← hζ, ← hξ]
  intro hU hV hC hZ hZ'
  exact Dynamic.centralizingDeterminant_square_of_centralizer_eq hroot
    r'.isCompatible.maximalSplit.isSplitSubtorus.1 ζ ξ hEq (l' ≫ q) hZ hZ' hU hV hC t ht
    bU bV bC hdetect

end Langlands.Global.AdelicGroupPoints
