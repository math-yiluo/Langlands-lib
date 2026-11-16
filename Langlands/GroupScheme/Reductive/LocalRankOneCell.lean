import Langlands.GroupScheme.Reductive.LocalSplitRootBaseChange
import Langlands.GroupScheme.Reductive.SplitLeviGluingRankOneFactors
import Langlands.GroupScheme.Reductive.RankOneCellData
import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion
import Langlands.GroupScheme.Reductive.RankOneRingCalculus
import Langlands.GroupScheme.SmoothProducts

/-! # Open cells from fieldwise rank-one root support -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace LocalRankOneCell

section Field

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G)

/-- When every root is one of an opposite pair, the positive dynamic factor
for a positive cocharacter is the intrinsic positive root subgroup. -/
theorem unipotent_eq_root_of_root_support (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (α : characterLattice T) (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T α ν)
    (hsupport : ∀ β ∈ roots (T := T) i, β = α ∨ β = -α) :
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) =
      RelativeRoot.subgroup i α := by
  let : ConnectedSpace G.X.left := hG.connectedSpace
  apply LeviGluing.unipotent_eq_root_of_positiveRoots_on_ray hT i ν α hpos
  intro β hβ hβpos
  rcases hsupport β hβ with rfl | rfl
  · exact ⟨1, by decide, one_nsmul _⟩
  · simp only [map_neg, LinearMap.neg_apply] at hβpos
    omega

/-- The opposite root maps and maximal torus give an open triple cell in
an actual connected reductive field group with exactly two roots. -/
theorem isOpenImmersion_tripleCell_of_root_support
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hmax : IsMaximalTorus i) (α : characterLattice T) (ν : cocharacterLattice T)
    (hα : α ∈ roots (T := T) i) (hpos : 0 < latticePairing T α ν)
    (hsupport : ∀ β ∈ roots (T := T) i, β = α ∨ β = -α)
    {M U : GroupScheme (Spec (CommRingCat.of k))} {xm : M ⟶ G} {xp : U ⟶ G}
    (hm : (RelativeRoot.subgroup i (-α)).IsRepresentedBy xm)
    (hp : (RelativeRoot.subgroup i α).IsRepresentedBy xp) :
    IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left := by
  have hdep : ¬ LinearIndependent ℤ ![α, α] := by
    intro h
    have hz := h.injective (show (![α, α] : Fin 2 → characterLattice T) 0 =
      (![α, α] : Fin 2 → characterLattice T) 1 from rfl)
    exact (by decide : (0 : Fin 2) ≠ 1) hz
  have hrank : ∀ β ∈ roots (T := T) i, ∀ delta ∈ roots (T := T) i,
      ¬ LinearIndependent ℤ ![β, delta] := by
    intro β hβ delta hdelta
    rcases hsupport β hβ with rfl | rfl <;>
      rcases hsupport delta hdelta with rfl | rfl <;>
      simpa only [LinearIndependent.pair_neg_left_iff,
        LinearIndependent.pair_neg_right_iff] using hdep
  have hz := rankOne_centralizer_isRepresentedBy
    dynamicCentralizerReductive hG hT i hmax hrank α hα ν hpos.ne'
  have hplus := unipotent_eq_root_of_root_support i hG hT α ν hpos hsupport
  have hminus := unipotent_eq_root_of_root_support i hG hT (-α) (-ν)
    (by simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hpos)
    (fun β hβ => by
      simpa only [neg_neg, or_comm] using hsupport β hβ)
  have hneg : Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ ν = -ν := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
  apply Dynamic.isOpenImmersion_tripleCellMultiplication
    (CommGroupScheme.groupHom ν ≫ i)
  · rw [← Category.assoc]
    change (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ ν) ≫ i)).IsRepresentedBy xm
    rw [hneg, hminus]
    exact hm
  · exact hz
  · rw [hplus]
    exact hp

end Field

end LocalRankOneCell

namespace Dynamic

/-- A change of the three subgroup sources commutes with their multiplication. -/
theorem tripleCellMultiplication_precomp {S : Scheme.{u}}
    {G M Z U M' Z' U' : GroupScheme S}
    (xm : M ⟶ G) (z : Z ⟶ G) (xp : U ⟶ G)
    (fm : M' ⟶ M) (fz : Z' ⟶ Z) (fp : U' ⟶ U) :
    (fm.hom.hom ⊗ₘ (fz.hom.hom ⊗ₘ fp.hom.hom)) ≫
        tripleCellMultiplication xm z xp =
      tripleCellMultiplication (fm ≫ xm) (fz ≫ z) (fp ≫ xp) := by
  simp only [tripleCellMultiplication, SubgroupFunctor.cellMultiplication,
    MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc,
    Grp.comp_hom_hom]

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {G M Z U : GroupScheme S}

/-- The product comparison identifies the pulled-back three-factor source
with the product of the actual pulled-back factors. -/
def tripleBaseChangeIso :
    ((baseChange b).obj M).X ⊗ (((baseChange b).obj Z).X ⊗ ((baseChange b).obj U).X) ≅
      (Over.pullback b).obj (M.X ⊗ (Z.X ⊗ U.X)) :=
  whiskerLeftIso ((baseChange b).obj M).X
      (Functor.Monoidal.μIso (Over.pullback b) Z.X U.X) ≪≫
    Functor.Monoidal.μIso (Over.pullback b) M.X (Z.X ⊗ U.X)

/-- Multiplication of three subgroup factors commutes with actual base change. -/
theorem tripleBaseChangeIso_hom_comp (xm : M ⟶ G) (z : Z ⟶ G) (xp : U ⟶ G) :
    (tripleBaseChangeIso b (M := M) (Z := Z) (U := U)).hom ≫
        (Over.pullback b).map (tripleCellMultiplication xm z xp) =
      tripleCellMultiplication ((baseChange b).map xm) ((baseChange b).map z)
        ((baseChange b).map xp) := by
  simp only [tripleBaseChangeIso, Iso.trans_hom, whiskerLeftIso_hom,
    Functor.Monoidal.μIso_hom, tripleCellMultiplication,
    SubgroupFunctor.cellMultiplication, Functor.map_mul, Functor.map_comp,
    MonObj.comp_mul, Category.assoc, Functor.Monoidal.μ_fst_assoc,
    Functor.Monoidal.μ_snd_assoc]
  dsimp only [baseChange, Functor.mapGrp]
  simp only [whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, Functor.Monoidal.μ_fst_assoc,
    Functor.Monoidal.μ_snd_assoc]
  rfl

end Dynamic

namespace LocalRankOneCell

open LocalSplitCell LocalSplitRootBaseChange

section BaseChange

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (I : Type u) [Fintype I]

/-- The standard additive-torus-additive source identifies with its actual
pullback, with the additive and torus coordinates preserved. -/
def standardTripleBaseChangeIso :
    (Ga A).X ⊗ ((splitTorus (Spec (CommRingCat.of A)) I).X ⊗ (Ga A).X) ≅
      (Over.pullback (algebraBaseMap R A)).obj
        ((Ga R).X ⊗ ((splitTorus (Spec (CommRingCat.of R)) I).X ⊗ (Ga R).X)) :=
  tensorIso ((Grp.forget _).mapIso (gaIso (R := R) A).symm)
      (tensorIso
        ((Grp.forget _).mapIso (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm)
        ((Grp.forget _).mapIso (gaIso (R := R) A).symm)) ≪≫
    Dynamic.tripleBaseChangeIso (algebraBaseMap R A)

/-- The comparison carries the pulled-back cell map to the cell map of the
standard base-changed root parametrizations and torus. -/
theorem standardTripleBaseChangeIso_hom_comp
    {G : GroupScheme (Spec (CommRingCat.of R))}
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (xm xp : Ga R ⟶ G) :
    (standardTripleBaseChangeIso (R := R) A I).hom ≫
        (Over.pullback (algebraBaseMap R A)).map
          (Dynamic.tripleCellMultiplication xm i xp) =
      Dynamic.tripleCellMultiplication (baseChangeRoot A xm)
        (splitTorus.baseChangeHom (K := A) G I i) (baseChangeRoot A xp) := by
  rw [standardTripleBaseChangeIso, Iso.trans_hom, Category.assoc,
    Dynamic.tripleBaseChangeIso_hom_comp]
  simpa only [tensorIso_hom, Functor.mapIso_hom, Iso.symm_hom,
    Grp.forget_map, baseChangeRoot, splitTorus.baseChangeHom] using
    Dynamic.tripleCellMultiplication_precomp
      ((GroupScheme.baseChange (algebraBaseMap R A)).map xm)
      ((GroupScheme.baseChange (algebraBaseMap R A)).map i)
      ((GroupScheme.baseChange (algebraBaseMap R A)).map xp)
      (gaIso (R := R) A).inv (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv
      (gaIso (R := R) A).inv

end BaseChange

section RingCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (a nu : I → ℤ) (xm xp : Ga R ⟶ G)

/-- The two-root condition on every field fibre makes the actual opposite-root
triple multiplication an open immersion on each such fibre. -/
theorem isOpenImmersion_fibre (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hpos : 0 < ∑ j, a j * nu j)
    (hm : IsRootParametrization i (-a) xm) (hp : IsRootParametrization i a xp)
    (k : Type u) [Field k] [Algebra R k]
    (hsupport : ∀ m : I → ℤ,
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        roots (T := splitTorus.commGroupScheme _ I)
          (splitTorus.baseChangeHom (K := k) G I i) ↔ m = a ∨ m = -a) :
    IsOpenImmersion ((Over.pullback (algebraBaseMap R k)).map
      (Dynamic.tripleCellMultiplication xm i xp)).left := by
  let : Smooth G.X.hom := hG.smooth
  let e := standardTripleBaseChangeIso (R := R) k I
  have hfield : IsOpenImmersion
      (Dynamic.tripleCellMultiplication (baseChangeRoot k xm)
        (splitTorus.baseChangeHom (K := k) G I i) (baseChangeRoot k xp)).left := by
    apply isOpenImmersion_tripleCell_of_root_support
      (splitTorus.baseChangeHom (K := k) G I i)
      (hG.isConnectedReductive_baseChange _) (isSplitTorus_splitTorus I)
      (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k)
      (splitTorus.exponentCharacter _ I a) (splitTorus.exponentCocharacter _ I nu)
    · exact (hsupport a).2 (Or.inl rfl)
    · simpa only [splitTorus.latticePairing_exponentCharacter_exponentCocharacter] using hpos
    · intro β hβ
      obtain ⟨m, rfl⟩ : ∃ m,
          splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m = β :=
        ⟨splitTorus.characterLatticeEquiv k I β, by
          rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
            AddEquiv.symm_apply_apply]⟩
      rcases (hsupport m).1 hβ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (by
          rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
            splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, map_neg])
    · simpa only [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, map_neg] using
        (isRootParametrization_baseChangeRoot k i (-a) xm hm).represents
    · exact (isRootParametrization_baseChangeRoot k i a xp hp).represents
  have heq := standardTripleBaseChangeIso_hom_comp (R := R) k I i xm xp
  have hcomp : IsOpenImmersion
      (e.hom.left ≫ ((Over.pullback (algebraBaseMap R k)).map
        (Dynamic.tripleCellMultiplication xm i xp)).left) := by
    change IsOpenImmersion (e.hom ≫ _).left
    rw [heq]
    exact hfield
  have hcancel : e.inv.left ≫ (e.hom.left ≫
      ((Over.pullback (algebraBaseMap R k)).map
        (Dynamic.tripleCellMultiplication xm i xp)).left) =
        ((Over.pullback (algebraBaseMap R k)).map
          (Dynamic.tripleCellMultiplication xm i xp)).left := by
    rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left,
      Category.id_comp]
  rw [← hcancel]
  infer_instance

/-- Fibrewise rank-one support gives an open root-torus-root cell over every
commutative ring, including rings with nilpotents. -/
theorem isOpenImmersion (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hpos : 0 < ∑ j, a j * nu j)
    (hm : IsRootParametrization i (-a) xm) (hp : IsRootParametrization i a xp)
    (hsupport : ∀ (k : Type u) [Field k] [Algebra R k] (m : I → ℤ),
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        roots (T := splitTorus.commGroupScheme _ I)
          (splitTorus.baseChangeHom (K := k) G I i) ↔ m = a ∨ m = -a) :
    IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left := by
  let : Smooth G.X.hom := hG.smooth
  have hGa : Smooth (Ga R).X.hom :=
    Corepresented.smooth_groupScheme_iff.mpr inferInstance
  let : Smooth ((Ga R).X ⊗
      ((splitTorus (Spec (CommRingCat.of R)) I).X ⊗ (Ga R).X)).hom :=
    smooth_tensor _ _ hGa (smooth_tensor _ _ (smooth_splitTorus I) hGa)
  apply Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise
  intro s
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  let : Algebra R ((Spec (CommRingCat.of R)).residueField s) := φ.hom.toAlgebra
  have hb : algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s) =
      (Spec (CommRingCat.of R)).fromSpecResidueField s :=
    Spec.map_preimage _
  have h := isOpenImmersion_fibre i a nu xm xp hG hmax hpos hm hp
    ((Spec (CommRingCat.of R)).residueField s)
    (hsupport ((Spec (CommRingCat.of R)).residueField s))
  rw [hb] at h
  exact h

end RingCell

end LocalRankOneCell

end Langlands.GroupScheme
