import Langlands.GroupScheme.Reductive.StarActionStatement
import Langlands.GroupScheme.Reductive.BasedRootDatumProjection
import Langlands.GroupScheme.Reductive.GeometricRootDatumComparison
import Langlands.GroupScheme.Reductive.RootDatumWeylProof
import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.LinearAlgebra.RootDatumWeylChambers

/-! # Independence of the star action from the Galois pinning data -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace StarActionIndependence

section RootData

variable {J J' M M' N N' : Type u} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
  [AddCommGroup N'] {P : RootDatum J M N} {P' : RootDatum J' M' N'}

/-- An equivalence of root data is determined by its weight map. -/
theorem equiv_ext_of_weightMap (f g : RootPairing.Equiv P P')
    (h : ∀ x, f.weightMap x = g.weightMap x) : f = g := by
  have hw : f.weightMap = g.weightMap := LinearMap.ext h
  ext x
  · exact h x
  · refine LinearEquiv.injective P.flip.toPerfPair ?_
    simp_rw [← RootPairing.Hom.weight_coweight_transpose_apply]
    exact congrFun (congrArg DFunLike.coe (congrArg LinearMap.dualMap hw))
      (P'.flip.toPerfPair x)
  · refine P'.root.injective ?_
    simp_rw [← RootPairing.Hom.root_weightMap_apply]
    exact h (P.root x)

/-- Conjugation of automorphisms by an equivalence of root data. -/
def conjAut (e : RootPairing.Equiv P P') : P.Aut →* P'.Aut where
  toFun x := e.comp (x.comp (RootPairing.Equiv.symm P P' e))
  map_one' := by
    apply equiv_ext_of_weightMap
    intro y
    change e.weightEquiv (e.weightEquiv.symm y) = y
    exact LinearEquiv.apply_symm_apply _ _
  map_mul' x z := by
    apply equiv_ext_of_weightMap
    intro y
    change e.weightEquiv (x.weightEquiv (z.weightEquiv (e.weightEquiv.symm y))) =
      e.weightEquiv (x.weightEquiv (e.weightEquiv.symm
        (e.weightEquiv (z.weightEquiv (e.weightEquiv.symm y)))))
    rw [LinearEquiv.symm_apply_apply]

theorem conjAut_weightMap (e : RootPairing.Equiv P P') (x : P.Aut) (y : M') :
    (conjAut e x).weightMap y = e.weightEquiv (x.weightEquiv (e.weightEquiv.symm y)) :=
  rfl

theorem conjAut_indexEquiv (e : RootPairing.Equiv P P') (x : P.Aut) (a : J') :
    (conjAut e x).indexEquiv a = e.indexEquiv (x.indexEquiv (e.indexEquiv.symm a)) :=
  rfl

/-- Conjugating a reflection gives the reflection at the transported root. -/
theorem conjAut_reflection (e : RootPairing.Equiv P P') (i : J) :
    conjAut e (RootPairing.Equiv.reflection P i) =
      RootPairing.Equiv.reflection P' (e.indexEquiv i) := by
  apply equiv_ext_of_weightMap
  intro x
  change e.weightEquiv (P.reflection i (e.weightEquiv.symm x)) =
    P'.reflection (e.indexEquiv i) x
  rw [e.weightEquiv_reflection, LinearEquiv.apply_symm_apply]

/-- Conjugation carries the Weyl group into the Weyl group. -/
theorem conjAut_mem_weylGroup (e : RootPairing.Equiv P P') {w : P.Aut}
    (hw : w ∈ P.weylGroup) : conjAut e w ∈ P'.weylGroup := by
  induction hw using RootPairing.weylGroup.induction with
  | mem i =>
    rw [conjAut_reflection]
    exact P'.reflection_mem_weylGroup _
  | one =>
    rw [map_one]
    exact one_mem _
  | mul a b ha hb ia ib =>
    rw [map_mul]
    exact mul_mem ia ib

/-- Composing with an automorphism on the right is composing with its conjugate on
the left. -/
theorem comp_eq_conjAut_comp (e : RootPairing.Equiv P P') (x : P.Aut) :
    e.comp x = (conjAut e x).comp e := by
  apply equiv_ext_of_weightMap
  intro y
  change e.weightEquiv (x.weightEquiv y) =
    e.weightEquiv (x.weightEquiv (e.weightEquiv.symm (e.weightEquiv y)))
  rw [LinearEquiv.symm_apply_apply]

/-- An equivalence of root data preserving positivity of roots for two bases carries the
simple roots of the first base exactly onto the simple roots of the second. -/
theorem mem_support_iff_of_isPos [Finite J] [Finite J'] (B : P.Base) (B' : P'.Base)
    (e : RootPairing.Equiv P P') (hpos : ∀ j, B'.IsPos (e.indexEquiv j) ↔ B.IsPos j)
    (a : J) : a ∈ B.support ↔ e.indexEquiv a ∈ B'.support := by
  rw [RootPairing.Base.mem_support_iff_positive_indecomposable P B,
    RootPairing.Base.mem_support_iff_positive_indecomposable P' B', hpos]
  have hroot : ∀ j, P'.root (e.indexEquiv j) = e.weightEquiv (P.root j) := fun j =>
    (RootPairing.Hom.root_weightMap_apply P P' j e.toHom).symm
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, fun j' l' hj hl heq => ?_⟩
    obtain ⟨j, rfl⟩ := e.indexEquiv.surjective j'
    obtain ⟨l, rfl⟩ := e.indexEquiv.surjective l'
    rw [hpos] at hj hl
    apply h j l hj hl
    apply e.weightEquiv.injective
    rw [map_add, ← hroot, ← hroot, ← hroot]
    exact heq
  · rintro ⟨hi, h⟩
    refine ⟨hi, fun j l hj hl heq => ?_⟩
    apply h (e.indexEquiv j) (e.indexEquiv l) ((hpos j).mpr hj) ((hpos l).mpr hl)
    rw [hroot, hroot, hroot, heq, map_add]

end RootData

section Pinnings

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (p : SplitPinning G) (q : SplitPinning H)

/-- Conjugation by an equivalence preserving the chosen bases preserves based
automorphisms. -/
theorem conjAut_mem_basedRootDatumAut (e : RootPairing.Equiv p.rootDatum q.rootDatum)
    (he : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)
    {x : p.rootDatum.Aut} (hx : x ∈ p.basedRootDatumAut) :
    conjAut e x ∈ q.basedRootDatumAut := by
  intro a
  obtain ⟨a, rfl⟩ := e.indexEquiv.surjective a
  rw [conjAut_indexEquiv, Equiv.symm_apply_apply, ← he, ← he]
  exact hx a

/-- The based projections of an automorphism and of any element of the Weyl coset of
its conjugate correspond under a base-preserving equivalence. -/
theorem comp_basedRootDatumProjection (e : RootPairing.Equiv p.rootDatum q.rootDatum)
    (he : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)
    (x : p.rootDatum.Aut) (x' : q.rootDatum.Aut)
    (hx : x' * (conjAut e x)⁻¹ ∈ q.rootDatum.weylGroup) :
    e.comp (p.basedRootDatumProjection x).val =
      (q.basedRootDatumProjection x').val.comp e := by
  have hθ := p.basedRootDatumProjection_correction x
  have hb : conjAut e (p.basedRootDatumProjection x).val ∈ q.basedRootDatumAut :=
    conjAut_mem_basedRootDatumAut p q e he (p.basedRootDatumProjection x).property
  have hproj : q.basedRootDatumProjection x' = ⟨_, hb⟩ := by
    apply q.basedRootDatum_representative_unique x' _ _
      (q.basedRootDatumProjection_correction x')
    change conjAut e (p.basedRootDatumProjection x).val * x'⁻¹ ∈ q.rootDatum.weylGroup
    have heq : conjAut e (p.basedRootDatumProjection x).val * x'⁻¹ =
        conjAut e ((p.basedRootDatumProjection x).val * x⁻¹) *
          (x' * (conjAut e x)⁻¹)⁻¹ := by
      rw [map_mul, map_inv]
      group
    rw [heq]
    exact mul_mem (conjAut_mem_weylGroup e hθ) (inv_mem hx)
  rw [hproj, comp_eq_conjAut_comp]

/-- Some Weyl element corrects an arbitrary equivalence of the root data of two
split pinnings into one preserving the chosen bases. -/
theorem exists_weyl_comp_preserves_base (e₀ : RootPairing.Equiv p.rootDatum q.rootDatum) :
    ∃ w ∈ q.rootDatum.weylGroup, ∀ a,
      a ∈ p.base.support ↔ (RootPairing.Equiv.comp w e₀).indexEquiv a ∈ q.base.support := by
  classical
  let := Fintype.ofFinite q.rootIndex
  let := q.finite_rootDatum_weylGroup
  have hposp (i : p.rootIndex) :
      0 < p.rootDatum.root' i p.positiveCocharacter ↔ p.base.IsPos i := by
    change 0 < p.rootDatum.toLinearMap (p.rootDatum.root i) p.positiveCocharacter ↔ _
    rw [p.isRootDatum.1]
    exact p.latticePairing_root_positiveCocharacter_pos_iff i
  have hposq (i : q.rootIndex) :
      0 < q.rootDatum.root' i q.positiveCocharacter ↔ q.base.IsPos i := by
    change 0 < q.rootDatum.toLinearMap (q.rootDatum.root i) q.positiveCocharacter ↔ _
    rw [q.isRootDatum.1]
    exact q.latticePairing_root_positiveCocharacter_pos_iff i
  have hnep (i : p.rootIndex) : p.rootDatum.root' i p.positiveCocharacter ≠ 0 := by
    change p.rootDatum.toLinearMap (p.rootDatum.root i) p.positiveCocharacter ≠ 0
    rw [p.isRootDatum.1]
    exact p.latticePairing_root_positiveCocharacter_ne_zero i
  have hneq (i : q.rootIndex) : q.rootDatum.root' i q.positiveCocharacter ≠ 0 := by
    change q.rootDatum.toLinearMap (q.rootDatum.root i) q.positiveCocharacter ≠ 0
    rw [q.isRootDatum.1]
    exact q.latticePairing_root_positiveCocharacter_ne_zero i
  let g := e₀.coweightEquiv.symm p.positiveCocharacter
  have hg (i : q.rootIndex) : q.rootDatum.root' i g ≠ 0 := by
    obtain ⟨j, rfl⟩ := e₀.indexEquiv.surjective i
    rw [e₀.root'_coweightEquiv]
    exact hnep j
  obtain ⟨u, hu⟩ := Langlands.LinearAlgebra.RootDatumWeylChambers.exists_same_signs
    q.rootDatum Set.univ hneq hg
  refine ⟨u.val⁻¹, inv_mem (Langlands.LinearAlgebra.RootDatumWeylChambers.reflectionSubgroup_le
    q.rootDatum _ u.property), mem_support_iff_of_isPos p.base q.base _ (fun j => ?_)⟩
  have hu' := hu (u.val.indexEquiv.symm (e₀.indexEquiv j)) (Set.mem_univ _)
  have hr := u.val.root'_coweightEquiv (u.val.indexEquiv.symm (e₀.indexEquiv j))
    (u.val.coweightEquiv g)
  rw [LinearEquiv.symm_apply_apply, Equiv.apply_symm_apply] at hr
  change q.base.IsPos (u.val.indexEquiv.symm (e₀.indexEquiv j)) ↔ p.base.IsPos j
  rw [← hposq, hu', ← hr, e₀.root'_coweightEquiv, hposp]

end Pinnings


section Conjugation

variable {B : Scheme.{u}} {C C' C'' C₂ C₂' : CommGroupScheme B} {H H₂ : GroupScheme B}
  {i : C.toGrp ⟶ H} {j : C'.toGrp ⟶ H} {l : C''.toGrp ⟶ H}
  {i₂ : C₂.toGrp ⟶ H₂} {j₂ : C₂'.toGrp ⟶ H₂}

/-- If `g` conjugates `i` onto `j` through `φ`, then `g⁻¹` conjugates `j` onto `i` through
the inverse of `φ`. -/
theorem conj_inv {g : Over.mk (𝟙 B) ⟶ H.X} {φ : C ≅ C'}
    (h : i ≫ (H.innerIso g).hom = CommGroupScheme.groupHom φ.hom ≫ j) :
    j ≫ (H.innerIso g⁻¹).hom = CommGroupScheme.groupHom φ.symm.hom ≫ i := by
  rw [innerIso_inv_hom, Iso.comp_inv_eq, Category.assoc, h, ← Category.assoc]
  change j = CommGroupScheme.groupHom (φ.inv ≫ φ.hom) ≫ j
  rw [Iso.inv_hom_id]
  exact (Category.id_comp j).symm

/-- Conjugations compose: conjugating by `g` and then by `g'` is conjugating by `g' * g`. -/
theorem conj_mul {g g' : Over.mk (𝟙 B) ⟶ H.X} {φ : C ≅ C'} {ψ : C' ≅ C''}
    (h : i ≫ (H.innerIso g).hom = CommGroupScheme.groupHom φ.hom ≫ j)
    (h' : j ≫ (H.innerIso g').hom = CommGroupScheme.groupHom ψ.hom ≫ l) :
    i ≫ (H.innerIso (g' * g)).hom = CommGroupScheme.groupHom (φ ≪≫ ψ).hom ≫ l := by
  rw [innerIso_mul_hom, ← Category.assoc, h, Category.assoc, h', ← Category.assoc]
  rfl

/-- The point `n` conjugates the subgroup `i` onto the subgroup `j` through the
isomorphism `φ` of commutative group schemes. -/
def IsConjugatingPoint (i : C.toGrp ⟶ H) (j : C'.toGrp ⟶ H) (n : Over.mk (𝟙 B) ⟶ H.X)
    (φ : C ≅ C') : Prop :=
  i ≫ (H.innerIso n).hom = CommGroupScheme.groupHom φ.hom ≫ j

/-- A point conjugating one subgroup onto another keeps doing so after transport along an
ambient isomorphism compatible with isomorphisms of the two subgroups. -/
theorem IsConjugatingPoint.transport {n : Over.mk (𝟙 B) ⟶ H.X} {φ : C ≅ C'}
    (hn : IsConjugatingPoint i j n φ) (e : C ≅ C₂) (e' : C' ≅ C₂') (F : H ≅ H₂)
    (hi : i ≫ F.hom = CommGroupScheme.groupHom e.hom ≫ i₂)
    (hj : j ≫ F.hom = CommGroupScheme.groupHom e'.hom ≫ j₂) :
    IsConjugatingPoint i₂ j₂ (n ≫ F.hom.hom.hom) (e.symm ≪≫ φ ≪≫ e') := by
  have hi₂ : i₂ = CommGroupScheme.groupHom e.inv ≫ i ≫ F.hom := by
    rw [hi]
    change i₂ = CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ i₂
    rw [Iso.inv_hom_id]
    exact (Category.id_comp i₂).symm
  change i₂ ≫ (H₂.innerIso (n ≫ F.hom.hom.hom)).hom = _
  calc
    _ = (CommGroupScheme.groupHom e.inv ≫ i ≫ F.hom) ≫
        (H₂.innerIso (n ≫ F.hom.hom.hom)).hom := by rw [← hi₂]
    _ = CommGroupScheme.groupHom e.inv ≫ (i ≫ (H.innerIso n).hom) ≫ F.hom := by
      rw [Category.assoc, Category.assoc, ← innerIso_hom_comp]
      simp only [Category.assoc]
    _ = CommGroupScheme.groupHom e.inv ≫
        (CommGroupScheme.groupHom φ.hom ≫ j) ≫ F.hom := by rw [hn]
    _ = _ := by
      simp only [Category.assoc, hj]
      rfl

/-- Conjugation of subgroups is preserved by pullback of the point. -/
theorem IsConjugatingPoint.baseChangeBasePoint {S' : Scheme.{u}} (c : S' ⟶ B)
    {n : Over.mk (𝟙 B) ⟶ H.X} {φ : C ≅ C'} (hn : IsConjugatingPoint i j n φ) :
    IsConjugatingPoint ((GroupScheme.baseChange c).map i) ((GroupScheme.baseChange c).map j)
      (Langlands.GroupScheme.baseChangeBasePoint c H n)
      ((CommGroupScheme.baseChange c).mapIso φ) := by
  have h := congrArg (fun f => (GroupScheme.baseChange c).map f) hn
  change (GroupScheme.baseChange c).map i ≫
      (((GroupScheme.baseChange c).obj H).innerIso
        (Langlands.GroupScheme.baseChangeBasePoint c H n)).hom =
    (GroupScheme.baseChange c).map (CommGroupScheme.groupHom φ.hom) ≫
      (GroupScheme.baseChange c).map j
  simpa only [IsConjugatingPoint, Functor.map_comp, baseChange_innerIso_hom] using h

/-- Inverse points conjugate back through the inverse isomorphism. -/
theorem IsConjugatingPoint.inv {g : Over.mk (𝟙 B) ⟶ H.X} {φ : C ≅ C'}
    (h : IsConjugatingPoint i j g φ) : IsConjugatingPoint j i g⁻¹ φ.symm :=
  conj_inv h

/-- Conjugating points compose. -/
theorem IsConjugatingPoint.mul {g g' : Over.mk (𝟙 B) ⟶ H.X} {φ : C ≅ C'} {ψ : C' ≅ C''}
    (h : IsConjugatingPoint i j g φ) (h' : IsConjugatingPoint j l g' ψ) :
    IsConjugatingPoint i l (g' * g) (φ ≪≫ ψ) :=
  conj_mul h h'

end Conjugation

section Descent

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  {T T' : CommGroupScheme B}

/-- Canonical descent transport of characters intertwines precomposition with an
isomorphism `φ` and with the descent transport of `φ`. -/
theorem descentTransport_inv_comp
    (φ : (CommGroupScheme.baseChange b).obj T ≅ (CommGroupScheme.baseChange b).obj T')
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    ((CommGroupScheme.descentBaseChangeIso b a ha T).symm ≪≫
        (CommGroupScheme.baseChange a).mapIso φ ≪≫
          CommGroupScheme.descentBaseChangeIso b a ha T').inv ≫
        characterLattice.transport b a ha T χ =
      characterLattice.transport b a ha T' (φ.inv ≫ χ) := by
  change ((CommGroupScheme.descentBaseChangeIso b a ha T').inv ≫
      (CommGroupScheme.baseChange a).map φ.inv ≫
        (CommGroupScheme.descentBaseChangeIso b a ha T).hom) ≫
    (CommGroupScheme.descentBaseChangeIso b a ha T).inv ≫
      (CommGroupScheme.baseChange a).map χ ≫ (Gm.commBaseChangeIso a).hom = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change _ = (CommGroupScheme.descentBaseChangeIso b a ha T').inv ≫
    (CommGroupScheme.baseChange a).map (φ.inv ≫ χ) ≫ (Gm.commBaseChangeIso a).hom
  rw [Functor.map_comp, Category.assoc]

/-- If a point conjugates the base change of `i` onto the base change of `j` through `φ`,
its canonical descent transport does so through the descent transport of `φ`. -/
theorem IsConjugatingPoint.baseChange_descent {H : GroupScheme B} (i : T.toGrp ⟶ H)
    (j : T'.toGrp ⟶ H)
    {g : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj H).X}
    {φ : (CommGroupScheme.baseChange b).obj T ≅ (CommGroupScheme.baseChange b).obj T'}
    (hg : IsConjugatingPoint (C := (CommGroupScheme.baseChange b).obj T)
      (C' := (CommGroupScheme.baseChange b).obj T')
      ((GroupScheme.baseChange b).map i) ((GroupScheme.baseChange b).map j) g φ) :
    IsConjugatingPoint (C := (CommGroupScheme.baseChange b).obj T)
      (C' := (CommGroupScheme.baseChange b).obj T')
      ((GroupScheme.baseChange b).map i) ((GroupScheme.baseChange b).map j)
      (Langlands.GroupScheme.baseChangeBasePoint a ((GroupScheme.baseChange b).obj H) g ≫
        (descentBaseChangeIso b a ha H).hom.hom.hom)
      ((CommGroupScheme.descentBaseChangeIso b a ha T).symm ≪≫
        (CommGroupScheme.baseChange a).mapIso φ ≪≫
          CommGroupScheme.descentBaseChangeIso b a ha T') :=
  (hg.baseChangeBasePoint a).transport
    (CommGroupScheme.descentBaseChangeIso b a ha T)
    (CommGroupScheme.descentBaseChangeIso b a ha T')
    (descentBaseChangeIso b a ha H) (descentBaseChangeIso_naturality b a ha i)
    (descentBaseChangeIso_naturality b a ha j)

end Descent

section Pinned

variable {K : Type u} [Field K] {H : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom H.X.hom]

/-- The tori of two split pinnings of the same group are rationally conjugate. -/
theorem exists_conj (p q : SplitPinning H) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) (φ : p.torus ≅ q.torus),
      p.inclusion ≫ (H.innerIso g).hom = CommGroupScheme.groupHom φ.hom ≫ q.inclusion := by
  have hG := p.isConnectedReductive
  have := hG.smooth
  have := hG.connectedSpace
  obtain ⟨g, e, h⟩ := smoothMaximalSplitTorusConjugacy K H _ _ p.inclusion q.inclusion
    (p.isMaximalTorus.isMaximalSplitTorus p.isSplitTorus)
    (q.isMaximalTorus.isMaximalSplitTorus q.isSplitTorus)
  exact ⟨g, CommGroupScheme.isoOfGroupIso e, h⟩

/-- Two split pinnings of the same group admit a conjugating point whose induced
equivalence of root data carries the chosen base to the chosen base. -/
theorem exists_conj_based (p q : SplitPinning H) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) (φ : p.torus ≅ q.torus)
      (e : RootPairing.Equiv p.rootDatum q.rootDatum),
      p.inclusion ≫ (H.innerIso g).hom = CommGroupScheme.groupHom φ.hom ≫ q.inclusion ∧
      (∀ χ, e.weightMap χ = φ.inv ≫ χ) ∧
      (∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support) := by
  obtain ⟨g₀, φ₀, h₀⟩ := exists_conj p q
  have hsq := conj_inv h₀
  let e₀ : RootPairing.Equiv p.rootDatum q.rootDatum :=
    rootDatumEquivOfTorusCompatibleIso q.isConnectedReductive p.isConnectedReductive
      q.isSplitTorus p.isSplitTorus q.isMaximalTorus p.isMaximalTorus
      (H.innerIso g₀⁻¹) φ₀.symm hsq q.isRootDatum p.isRootDatum
  have he₀ (χ : characterLattice p.torus) : e₀.weightMap χ = φ₀.inv ≫ χ :=
    rootDatumEquivOfTorusCompatibleIso_weightMap q.isConnectedReductive p.isConnectedReductive
      q.isSplitTorus p.isSplitTorus q.isMaximalTorus p.isMaximalTorus
      (H.innerIso g₀⁻¹) φ₀.symm hsq q.isRootDatum p.isRootDatum χ
  obtain ⟨w, hw, hbase⟩ := exists_weyl_comp_preserves_base p q e₀
  let : IsClosedImmersion q.inclusion.hom.hom.left := q.isMaximalTorus.2.1
  have hW := (weylGroup K H q.isConnectedReductive q.torus q.isSplitTorus q.inclusion
    q.isMaximalTorus q.rootIndex q.rootDatum q.isRootDatum).1
  have hwi : RootPairing.Equiv.weightHom q.rootDatum w ∈
      weylImage q.inclusion := by
    rw [hW]
    exact Subgroup.mem_map_of_mem _ hw
  obtain ⟨n, hn⟩ := MonoidHom.mem_range.1 hwi
  have hτ := isNormalizingPoint_normalizingAut q.inclusion n
  refine ⟨n.val * g₀, φ₀ ≪≫ normalizingAut q.inclusion n, RootPairing.Equiv.comp w e₀,
    conj_mul h₀ hτ, fun χ => ?_, hbase⟩
  have h := DFunLike.congr_fun hn (e₀.weightMap χ)
  change (normalizingAut q.inclusion n).inv ≫ e₀.weightMap χ = w.weightMap (e₀.weightMap χ)
    at h
  change w.weightMap (e₀.weightMap χ) = ((normalizingAut q.inclusion n).inv ≫ φ₀.inv) ≫ χ
  rw [← h, he₀, Category.assoc]

/-- A rational point normalizing the torus of a split pinning acts on characters through an
element of the Weyl group of the root datum. -/
theorem exists_weyl_of_isNormalizingPoint (p : SplitPinning H)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X} {τ : p.torus ≅ p.torus}
    (hn : IsNormalizingPoint p.inclusion n τ) :
    ∃ w ∈ p.rootDatum.weylGroup, ∀ χ, w.weightMap χ = τ.inv ≫ χ := by
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  have hW := (weylGroup K H p.isConnectedReductive p.torus p.isSplitTorus p.inclusion
    p.isMaximalTorus p.rootIndex p.rootDatum p.isRootDatum).1
  let m : normalizerPoints p.inclusion := ⟨n, (mem_normalizerPoints p.inclusion).2 ⟨τ, hn⟩⟩
  have hmem : characterAut τ ∈ weylImage p.inclusion := by
    refine MonoidHom.mem_range.2 ⟨m, ?_⟩
    change characterAut (normalizingAut p.inclusion m) = _
    rw [(isNormalizingPoint_normalizingAut p.inclusion m).unique p.inclusion hn]
  rw [hW] at hmem
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.1 hmem
  exact ⟨w, hw, fun χ => DFunLike.congr_fun hwe χ⟩

end Pinned

local instance baseChangeAffine (k E : Type u) [Field k] [Field E] [Algebra k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

section Main

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

/-- The ordinary Galois action on characters is the Galois representation of the torus. -/
theorem galoisAction_weightMap_apply (d : GaloisPinningData k E G) (σ : E ≃ₐ[k] E)
    (χ : characterLattice d.toSplitPinning.torus) :
    (d.galoisAction σ).weightMap χ = characterLattice.galoisRepresentation k E d.torus σ χ :=
  LinearMap.congr_fun (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus_weightMap k E
    d.inclusion d.isSplitTorus d.isMaximalTorus.2.1 d.isRootDatum σ) χ

omit [LocallyOfFiniteType G.X.hom] in
/-- A conjugating point of the two tori, in the language of conjugating points. -/
theorem isConjugatingPoint_of_conj (d d' : GaloisPinningData k E G)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X}
    {φ : d.toSplitPinning.torus ≅ d'.toSplitPinning.torus}
    (hg : d.toSplitPinning.inclusion ≫
        (((GroupScheme.baseChange (algebraBaseMap k E)).obj G).innerIso g).hom =
      CommGroupScheme.groupHom φ.hom ≫ d'.toSplitPinning.inclusion) :
    IsConjugatingPoint (C := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj d.torus)
      (C' := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj d'.torus)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map d.inclusion)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map d'.inclusion) g φ :=
  hg

omit [LocallyOfFiniteType G.X.hom] in
/-- A point conjugating the torus of `d'` onto itself normalizes it. -/
theorem isNormalizingPoint_of_isConjugatingPoint (d' : GaloisPinningData k E G)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X}
    {τ : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj d'.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj d'.torus}
    (h : IsConjugatingPoint (C := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj d'.torus)
      (C' := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj d'.torus)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map d'.inclusion)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map d'.inclusion) n τ) :
    IsNormalizingPoint d'.toSplitPinning.inclusion n τ :=
  h

/-- If a Weyl element `w` acts on characters as the composite of `φ⁻¹` and an isomorphism
`ψ` intertwining the two Galois representations, then the Galois action for `d'` is `w`
times the conjugate of the Galois action for `d`. -/
theorem galoisAction_eq_weyl_mul (d d' : GaloisPinningData k E G)
    {φ ψ : d.toSplitPinning.torus ≅ d'.toSplitPinning.torus}
    (e : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum)
    (he : ∀ χ, e.weightMap χ = φ.inv ≫ χ) (σ : E ≃ₐ[k] E)
    (hψ : ∀ χ, ψ.inv ≫ characterLattice.galoisRepresentation k E d.torus σ χ =
      characterLattice.galoisRepresentation k E d'.torus σ (φ.inv ≫ χ))
    (w : d'.toSplitPinning.rootDatum.Aut)
    (hw : ∀ χ, w.weightMap χ = (φ.symm ≪≫ ψ).inv ≫ χ) :
    d'.galoisAction σ = w * conjAut e (d.galoisAction σ) := by
  apply equiv_ext_of_weightMap
  intro y
  obtain ⟨χ, rfl⟩ := e.weightEquiv.surjective y
  change (d'.galoisAction σ).weightMap (e.weightMap χ) =
    w.weightMap (e.weightMap ((d.galoisAction σ).weightMap
      (e.weightEquiv.symm (e.weightEquiv χ))))
  rw [LinearEquiv.symm_apply_apply, galoisAction_weightMap_apply,
    galoisAction_weightMap_apply, he, he, hw, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.hom_inv_id_assoc, hψ]

/-- A conjugating point whose root-datum equivalence preserves the chosen bases
intertwines the two star actions. -/
theorem starAction_intertwine (d d' : GaloisPinningData k E G)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X}
    {φ : d.toSplitPinning.torus ≅ d'.toSplitPinning.torus}
    (e : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum)
    (hg : d.toSplitPinning.inclusion ≫
        (((GroupScheme.baseChange (algebraBaseMap k E)).obj G).innerIso g).hom =
      CommGroupScheme.groupHom φ.hom ≫ d'.toSplitPinning.inclusion)
    (he : ∀ χ, e.weightMap χ = φ.inv ≫ χ)
    (hb : ∀ a, a ∈ d.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d'.toSplitPinning.base.support)
    (σ : E ≃ₐ[k] E) :
    RootPairing.Equiv.comp e (d.starAction σ).val =
      RootPairing.Equiv.comp (d'.starAction σ).val e := by
  -- The types of `hσ` and `hn` are left to be inferred, so that the Galois-transported
  -- point and isomorphism keep the syntactic form produced by `baseChange_descent`.
  have hg' := isConjugatingPoint_of_conj d d' hg
  have hσ := hg'.baseChange_descent (algebraBaseMap k E) (galoisBaseMap k E σ)
    (galoisBaseMap_over k E σ) d.inclusion d'.inclusion
  have hn := hg'.inv.mul hσ
  obtain ⟨w, hw, hwχ⟩ := exists_weyl_of_isNormalizingPoint d'.toSplitPinning
    (isNormalizingPoint_of_isConjugatingPoint d' hn)
  have heq := galoisAction_eq_weyl_mul d d' e he σ (fun χ => by
    rw [characterLattice.galoisRepresentation_apply,
      characterLattice.galoisRepresentation_apply]
    exact descentTransport_inv_comp (T := d.torus) (T' := d'.torus) (algebraBaseMap k E)
      (galoisBaseMap k E σ) (galoisBaseMap_over k E σ) φ χ) w hwχ
  have hx : d'.galoisAction σ * (conjAut e (d.galoisAction σ))⁻¹ ∈
      d'.toSplitPinning.rootDatum.weylGroup := by
    rw [heq, mul_inv_cancel_right]
    exact hw
  exact comp_basedRootDatumProjection d.toSplitPinning d'.toSplitPinning e hb
    (d.galoisAction σ) (d'.galoisAction σ) hx

end Main

/-- **Independence of the star action.** -/
theorem starActionIndependence : StarActionIndependenceStatement.{u} := by
  intro k E _ _ _ G _ _ d d'
  obtain ⟨g, φ, e, hg, he, hb⟩ := exists_conj_based d.toSplitPinning d'.toSplitPinning
  refine ⟨g, φ, e, hg, ?_, hb, starAction_intertwine d d' e hg he hb⟩
  funext χ
  exact he χ

end StarActionIndependence

end Langlands.GroupScheme
