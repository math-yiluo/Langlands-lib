/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalAlgebraRingAdjoint
import WeilConjectures.AlgebraicGeometry.SmoothPurity.IdealTensorPullbackComparison
import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.PushforwardHomAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Flat base change of the conormal graded algebra

Source: Stacks Project, Divisors, Tags 0634 and 0635, closed immersion case
(blueprint: lem-pur-conormal-algebra-flat-base-change).

## Main definitions

* `adjointPiece`: the adjoint of a homogeneous comparison, on the ambient schemes.
* `IsBaseChangeMap`: the graded algebra comparison specified by its affine tensor formula.

## Main statements

* `existsUnique_baseChangeMap`: existence, uniqueness, surjectivity, and flat isomorphism.

An algebra map out of a tensor pullback is encoded by its underlying module map and
its adjoint ring-sheaf map over the structure-sheaf map. This is the usual universal
property of algebra scalar extension; the homogeneous maps specify its grading.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback

namespace AlgebraicGeometry.ConormalGradedAlgebra

local instance conormalRestrictionSMul {Y : Scheme.{u}} (M : Y.Modules)
    {U V : Y.Opens} (j : U ⟶ V) :
    SMul Γ(Y, U)
      ((ModuleCat.restrictScalars (Y.ringCatSheaf.obj.map j.op).hom).obj
        (M.val.obj (op U))) :=
  inferInstanceAs (SMul Γ(Y, U) Γ(M, U))

variable {X Z X' Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
  [IsClosedImmersion i] [IsClosedImmersion i']
  (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')

/-- The adjoint homogeneous comparison, with the commutative square implementing the
identification of the two pushforwards. The adjunction units send a representative to
its pure tensor with one. Source: Stacks Project, Divisors, Tag 0634
(blueprint: lem-pur-conormal-algebra-flat-base-change). -/
def adjointPiece (n : ℕ) (d : (tensorPullback f).obj (piece i' n) ⟶ piece i n) :
    power i' n ⟶ (pushforward (i ≫ g)).obj (piece i n) :=
  (Classical.choose (exists_tensorPullbackAdjunction i')).unit.app (power i' n) ≫
    (pushforward i').map
      ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (piece i' n) ≫
        (pushforward f).map d) ≫
    (pushforwardComp f i').hom.app (piece i n) ≫
    (pushforwardCongr h.symm).hom.app (piece i n)

/-- Specification of the canonical conormal-algebra comparison. A ring-sheaf adjoint
makes the module map an algebra map; homogeneous maps make it graded. The affine formula
uses ideal-power representatives and arbitrary scalar factors, hence says precisely
`[a] tensor r` maps to `[g-sharp(a) * r]` under the recorded conormal identifications.
The last two equations normalize degrees zero and one using the existing canonical maps.
Source: Stacks Project, Divisors, Tags 0634 and 0635
(blueprint: lem-pur-conormal-algebra-flat-base-change). -/
def IsBaseChangeMap (A : Presentation i) (A' : Presentation i')
    (c : (tensorPullback f).obj A'.algebra.toModule ⟶ A.algebra.toModule) : Prop :=
  ∃ (ρ : A'.algebra.right ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj A.algebra.right)
    (d : ∀ n : ℕ, (tensorPullback f).obj (piece i' n) ⟶ piece i n),
    (A'.algebra.hom ≫ ρ =
      (⟨f.c⟩ : Z'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Z.sheaf) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map A.algebra.hom) ∧
    (∀ (V : Z'.Opens) (a : A'.algebra.right.obj.obj (op V)),
      c.val.app (op (f ⁻¹ᵁ V))
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
          A'.algebra.toModule).val.app (op V) a) = ρ.hom.app (op V) a) ∧
    (∀ n : ℕ, (tensorPullback f).map (A'.inclusion n) ≫ c = d n ≫ A.inclusion n) ∧
    (∀ (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1)
      (n : ℕ) (a : (power i' n).val.obj (op U'.1)) (r : Γ(X, U.1)),
      ∃ b : (power i n).val.obj (op U.1),
        (powerInclusion i n).val.app (op U.1) b =
          g.appLE U'.1 U.1 H ((powerInclusion i' n).val.app (op U'.1) a) * r ∧
        i.app U.1 r •
          (piece i n).val.map (homOfLE (i.preimage_mono H)).op
            ((adjointPiece i i' g f h n (d n)).val.app (op U'.1) a) =
          representative i n U.1 b) ∧
    (d 0 ≫ tensorPullbackObjUnitToUnit i =
      (tensorPullback f).map (tensorPullbackObjUnitToUnit i') ≫
        tensorPullbackObjUnitToUnit f) ∧
    d 1 = Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [IsClosedImmersion i] in
private theorem baseChangeIdeal (hc : IsLimit (PullbackCone.mk i f h)) :
    i.ker = i'.ker.comap g := by
  let p : IsPullback i f g i' := IsPullback.of_isLimit hc
  rw [← p.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

private theorem powerComparison (hc : IsLimit (PullbackCone.mk i f h))
    (A : Presentation i) (A' : Presentation i') (n : ℕ) :
    ∃ γ : (tensorPullback g).obj (power i' n) ⟶ power i n,
      γ ≫ powerInclusion i n =
        (tensorPullback g).map (powerInclusion i' n) ≫ tensorPullbackObjUnitToUnit g ∧
      Epi γ ∧ (Flat g → IsIso γ) := by
  classical
  obtain ⟨e, he⟩ := A.powerIdentification n
  obtain ⟨e', he'⟩ := A'.powerIdentification n
  have hk : (i'.ker ^ n).comap g = i.ker ^ n := by
    rw [Scheme.IdealSheafData.comap_pow, baseChangeIdeal i i' g f h hc]
  obtain ⟨δ, hδ, _⟩ := existsUnique_idealTensorPullbackComparison g (i'.ker ^ n)
  have transport : ∀ (J K : X.IdealSheafData), J = K →
      ∃ k : J.toModules ≅ K.toModules, k.hom ≫ K.toModulesι = J.toModulesι := by
    intro J K q
    subst K
    exact ⟨Iso.refl _, Category.id_comp _⟩
  obtain ⟨k, hkι⟩ := transport ((i'.ker ^ n).comap g) (i.ker ^ n) hk
  have heinv : e.inv ≫ powerInclusion i n = (i.ker ^ n).toModulesι := by
    rw [← he, Iso.inv_hom_id_assoc]
  let γ := (tensorPullback g).map e'.hom ≫ δ ≫ k.hom ≫ e.inv
  have hγ : γ ≫ powerInclusion i n =
      (tensorPullback g).map (powerInclusion i' n) ≫ tensorPullbackObjUnitToUnit g := by
    dsimp only [γ]
    simp only [Category.assoc]
    rw [heinv, hkι, hδ.1]
    rw [← Functor.map_comp_assoc, he']
  have : Epi δ := hδ.2.1
  have : Epi γ := by dsimp only [γ]; infer_instance
  refine ⟨γ, hγ, inferInstance, ?_⟩
  intro hg
  have : IsIso δ := hδ.2.2 hg
  dsimp only [γ]
  infer_instance

private def pieceAdjunction :
    tensorPullback i' ⋙ tensorPullback f ⊣ pushforward (i ≫ g) :=
  ((Classical.choose (exists_tensorPullbackAdjunction i')).comp
    (Classical.choose (exists_tensorPullbackAdjunction f))).ofNatIsoRight
      (pushforwardComp f i' ≪≫ pushforwardCongr h.symm)

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
private theorem pieceAdjunction_apply (n : ℕ)
    (d : (tensorPullback f).obj (piece i' n) ⟶ piece i n) :
    (pieceAdjunction i i' g f h).homEquiv (power i' n) (piece i n) d =
      adjointPiece i i' g f h n d := by
  dsimp only [pieceAdjunction]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change (Classical.choose (exists_tensorPullbackAdjunction i')).homEquiv _ _
    ((Classical.choose (exists_tensorPullbackAdjunction f)).homEquiv _ _ d) ≫ _ = _
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [adjointPiece, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rfl

private theorem adjunction_map_comparison {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} {P : D ⥤ C} (L : F ⊣ P) (R : G ⊣ P)
    {M : C} {N : D} (a : G.obj M ⟶ N) :
    ∃ d : F.obj M ⟶ N, L.homEquiv M N d = R.homEquiv M N a ∧
      (Epi a → Epi d) ∧ (IsIso a → IsIso d) := by
  let e := L.leftAdjointUniq R
  let d := e.hom.app M ≫ a
  refine ⟨d, ?_, ?_, ?_⟩
  · dsimp only [d, e]
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit]
  · intro ha
    have := ha
    dsimp only [d]
    infer_instance
  · intro ha
    have := ha
    dsimp only [d]
    infer_instance

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
private theorem pieceComparisonOfPower (n : ℕ)
    (γ : (tensorPullback g).obj (power i' n) ⟶ power i n) :
    ∃ d : (tensorPullback f).obj (piece i' n) ⟶ piece i n,
      adjointPiece i i' g f h n d =
        (Classical.choose (exists_tensorPullbackAdjunction g)).unit.app (power i' n) ≫
          (pushforward g).map
            (γ ≫ (Classical.choose (exists_tensorPullbackAdjunction i)).unit.app (power i n)) ≫
          (pushforwardComp i g).hom.app (piece i n) ∧
      (Epi γ → Epi d) ∧ (IsIso γ → IsIso d) := by
  let L := pieceAdjunction i i' g f h
  let adji := Classical.choose (exists_tensorPullbackAdjunction i)
  let adjg := Classical.choose (exists_tensorPullbackAdjunction g)
  let R := (adjg.comp adji).ofNatIsoRight (pushforwardComp i g)
  obtain ⟨d, he, hdepi, hdiso⟩ :=
    adjunction_map_comparison L R ((tensorPullback i).map γ)
  refine ⟨d, ?_, ?_, ?_⟩
  · rw [← pieceAdjunction_apply i i' g f h n d]
    change L.homEquiv _ _ d = _
    rw [he]
    dsimp only [R]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change adjg.homEquiv _ _ (adji.homEquiv _ _ ((tensorPullback i).map γ)) ≫ _ = _
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    rw [← adji.unit_naturality γ, Category.assoc]
    rfl
  · intro hγ
    have := hγ
    let := adji.isLeftAdjoint
    exact hdepi inferInstance
  · intro hγ
    have := hγ
    exact hdiso inferInstance

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
private theorem powerComparison_unit (n : ℕ)
    (γ : (tensorPullback g).obj (power i' n) ⟶ power i n)
    (hγ : γ ≫ powerInclusion i n =
      (tensorPullback g).map (powerInclusion i' n) ≫ tensorPullbackObjUnitToUnit g)
    (U' : X'.Opens) (a : (power i' n).val.obj (op U')) :
    (powerInclusion i n).app (g ⁻¹ᵁ U')
      (γ.app (g ⁻¹ᵁ U')
        (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
          (power i' n)).app U' a)) =
      g.app U' ((powerInclusion i' n).app U' a) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  have he : adj.homEquiv _ _ (γ ≫ powerInclusion i n) =
      powerInclusion i' n ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
    rw [hγ, Adjunction.homEquiv_naturality_left]
    exact congrArg (fun q ↦ powerInclusion i' n ≫ q)
      (Equiv.apply_symm_apply (adj.homEquiv _ _) _)
  rw [Adjunction.homEquiv_unit] at he
  exact congrArg (fun q ↦ q.app U' a) he

omit [IsClosedImmersion i] in
private theorem representative_smul (n : ℕ) (U : X.Opens) (r : Γ(X, U))
    (a : (power i n).val.obj (op U)) :
    representative i n U (r • a) = i.app U r • representative i n U a := by
  exact (Hom.app_smul
    ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app (power i n)) r a).trans
      (pushforward_smul_def i (piece i n) U r _)

private def PieceFormula (n : ℕ)
    (d : (tensorPullback f).obj (piece i' n) ⟶ piece i n) : Prop :=
  ∀ (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1)
    (a : (power i' n).val.obj (op U'.1)) (r : Γ(X, U.1)),
    ∃ b : (power i n).val.obj (op U.1),
      (powerInclusion i n).val.app (op U.1) b =
        g.appLE U'.1 U.1 H ((powerInclusion i' n).val.app (op U'.1) a) * r ∧
      i.app U.1 r • (piece i n).val.map (homOfLE (i.preimage_mono H)).op
        ((adjointPiece i i' g f h n d).val.app (op U'.1) a) =
          representative i n U.1 b

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
private theorem pieceFormula_of_powerComparison (n : ℕ)
    (γ : (tensorPullback g).obj (power i' n) ⟶ power i n)
    (hγ : γ ≫ powerInclusion i n =
      (tensorPullback g).map (powerInclusion i' n) ≫ tensorPullbackObjUnitToUnit g)
    (d : (tensorPullback f).obj (piece i' n) ⟶ piece i n)
    (hd : adjointPiece i i' g f h n d =
      (Classical.choose (exists_tensorPullbackAdjunction g)).unit.app (power i' n) ≫
        (pushforward g).map
          (γ ≫ (Classical.choose (exists_tensorPullbackAdjunction i)).unit.app (power i n)) ≫
        (pushforwardComp i g).hom.app (piece i n)) :
    PieceFormula i i' g f h n d := by
  intro U U' H a r
  let s : (power i n).val.obj (op U.1) := (power i n).val.map (homOfLE H).op
    (γ.app (g ⁻¹ᵁ U'.1)
      (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
        (power i' n)).app U'.1 a))
  refine ⟨r • s, ?_, ?_⟩
  · change (powerInclusion i n).app U.1 (r • s) = _
    rw [Hom.app_smul]
    change r * (@id Γ(X, U.1) ((powerInclusion i n).app U.1 s)) = _
    dsimp only [s]
    erw [Hom.app_presheaf_map, powerComparison_unit i i' g n γ hγ]
    exact mul_comm _ _
  · rw [hd]
    have hu := (Classical.choose (exists_tensorPullbackAdjunction i)).unit.app (power i n)
      |>.val.naturality (homOfLE H).op
    have hus := congrArg (fun q ↦ q (γ.app (g ⁻¹ᵁ U'.1)
      (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
        (power i' n)).app U'.1 a))) hu
    rw [representative_smul]
    congr 1
    exact hus.symm

omit [IsClosedImmersion i'] in
private theorem pieceFormula_unique (A : Presentation i) (n : ℕ)
    (d e : (tensorPullback f).obj (piece i' n) ⟶ piece i n)
    (hd : PieceFormula i i' g f h n d) (he : PieceFormula i i' g f h n e) : d = e := by
  obtain ⟨E, hE⟩ := A.powerIdentification n
  have hm : Mono (powerInclusion i n) := by rw [← hE]; infer_instance
  have hmval : Mono (powerInclusion i n).val := (SheafOfModules.forget _).map_mono _
  have hinj (U : X.Opens) : Function.Injective ((powerInclusion i n).val.app (op U)) :=
    PresheafOfModules.injective_of_mono _ _
  apply ((pieceAdjunction i i' g f h).homEquiv (power i' n) (piece i n)).injective
  rw [pieceAdjunction_apply, pieceAdjunction_apply]
  apply Scheme.Modules.hom_ext
  intro W
  ext a
  let Charts := {p : X.affineOpens × X'.affineOpens //
    p.2.1 ≤ W ∧ p.1.1 ≤ g ⁻¹ᵁ p.2.1}
  let V (t : Charts) : Z.Opens := i ⁻¹ᵁ t.1.1.1
  have hV (t : Charts) : V t ≤ (i ≫ g) ⁻¹ᵁ W :=
    i.preimage_mono (t.2.2.trans (g.preimage_mono t.2.1))
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨(piece i n).presheaf, (piece i n).isSheaf⟩
    V ((i ≫ g) ⁻¹ᵁ W) (fun t ↦ homOfLE (hV t)) ?_ _ _ ?_
  · intro z hz
    obtain ⟨U', hU', hzU', hU'W⟩ := exists_isAffineOpen_mem_and_subset
      (show g (i z) ∈ W from hz)
    obtain ⟨U, hU, hzU, hUU'⟩ := exists_isAffineOpen_mem_and_subset
      (show i z ∈ g ⁻¹ᵁ U' from hzU')
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨(⟨U, hU⟩, ⟨U', hU'⟩), hU'W, hUU'⟩, hzU⟩
  · intro t
    let a' := (power i' n).val.map (homOfLE t.2.1).op a
    obtain ⟨b, hb, hdb⟩ := hd t.1.1 t.1.2 t.2.2 a' 1
    obtain ⟨b', hb', heb⟩ := he t.1.1 t.1.2 t.2.2 a' 1
    have hbb : b = b' := hinj _ (hb.trans hb'.symm)
    have hres (q : (tensorPullback f).obj (piece i' n) ⟶ piece i n) :
        (piece i n).val.map (homOfLE (hV t)).op
          ((adjointPiece i i' g f h n q).val.app (op W) a) =
        (piece i n).val.map (homOfLE (i.preimage_mono t.2.2)).op
          ((adjointPiece i i' g f h n q).val.app (op t.1.2.1) a') := by
      have hn := Hom.app_presheaf_map (adjointPiece i i' g f h n q)
        (homOfLE t.2.1) a
      dsimp only [a']
      erw [hn]
      change (piece i n).presheaf.map (homOfLE (hV t)).op _ =
        (piece i n).presheaf.map (homOfLE (i.preimage_mono t.2.2)).op
          ((piece i n).presheaf.map _ _)
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      congr 1
    change (piece i n).val.map (homOfLE (hV t)).op
      ((adjointPiece i i' g f h n d).val.app (op W) a) =
      (piece i n).val.map (homOfLE (hV t)).op
        ((adjointPiece i i' g f h n e).val.app (op W) a)
    rw [hres d, hres e]
    rw [hbb] at hdb
    simpa only [map_one, one_smul] using hdb.trans heb.symm

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
private theorem degreeZeroOfPower
    (γ : (tensorPullback g).obj (power i' 0) ⟶ power i 0)
    (hγ : γ ≫ powerInclusion i 0 =
      (tensorPullback g).map (powerInclusion i' 0) ≫ tensorPullbackObjUnitToUnit g)
    (d : (tensorPullback f).obj (piece i' 0) ⟶ piece i 0)
    (hd : adjointPiece i i' g f h 0 d =
      (Classical.choose (exists_tensorPullbackAdjunction g)).unit.app (power i' 0) ≫
        (pushforward g).map
          (γ ≫ (Classical.choose (exists_tensorPullbackAdjunction i)).unit.app (power i 0)) ≫
        (pushforwardComp i g).hom.app (piece i 0)) :
    d ≫ tensorPullbackObjUnitToUnit i =
      (tensorPullback f).map (tensorPullbackObjUnitToUnit i') ≫
        tensorPullbackObjUnitToUnit f := by
  let adji := Classical.choose (exists_tensorPullbackAdjunction i)
  let adjg := Classical.choose (exists_tensorPullbackAdjunction g)
  let adjf := Classical.choose (exists_tensorPullbackAdjunction f)
  let adji' := Classical.choose (exists_tensorPullbackAdjunction i')
  let L := pieceAdjunction i i' g f h
  let R := (adjg.comp adji).ofNatIsoRight (pushforwardComp i g)
  have hγ' : γ = tensorPullbackObjUnitToUnit g := by
    have hγ₀ : γ ≫ 𝟙 (SheafOfModules.unit X.ringCatSheaf) =
        (tensorPullback g).map (𝟙 (SheafOfModules.unit X'.ringCatSheaf)) ≫
          tensorPullbackObjUnitToUnit g := hγ
    calc
      γ = γ ≫ 𝟙 _ := (Category.comp_id γ).symm
      _ = _ := hγ₀
      _ = 𝟙 _ ≫ tensorPullbackObjUnitToUnit g :=
        congrArg (fun k ↦ k ≫ tensorPullbackObjUnitToUnit g)
          ((tensorPullback g).map_id (SheafOfModules.unit X'.ringCatSheaf))
      _ = _ := Category.id_comp _
  have he : L.homEquiv _ _ d = R.homEquiv _ _ ((tensorPullback i).map γ) := by
    rw [show L.homEquiv _ _ d = adjointPiece i i' g f h 0 d from
      pieceAdjunction_apply i i' g f h 0 d, hd]
    dsimp only [R]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change _ = adjg.homEquiv _ _ (adji.homEquiv _ _ ((tensorPullback i).map γ)) ≫ _
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    rw [← adji.unit_naturality γ, Category.assoc]
    rfl
  apply (L.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, he,
    ← Adjunction.homEquiv_naturality_right]
  dsimp only [R, L, pieceAdjunction]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change adjg.homEquiv _ _ (adji.homEquiv _ _
    ((tensorPullback i).map γ ≫ tensorPullbackObjUnitToUnit i)) ≫ _ =
    adji'.homEquiv _ _ (adjf.homEquiv _ _
      ((tensorPullback f).map (tensorPullbackObjUnitToUnit i') ≫
        tensorPullbackObjUnitToUnit f)) ≫ _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left, hγ']
  erw [show adji.homEquiv _ _ (tensorPullbackObjUnitToUnit i) =
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom from
        (adji.homEquiv _ _).apply_symm_apply _,
    show adjf.homEquiv _ _ (tensorPullbackObjUnitToUnit f) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom from
        (adjf.homEquiv _ _).apply_symm_apply _]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  erw [show adjg.homEquiv _ _ (tensorPullbackObjUnitToUnit g) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom from
        (adjg.homEquiv _ _).apply_symm_apply _,
    show adji'.homEquiv _ _ (tensorPullbackObjUnitToUnit i') =
      SheafOfModules.unitToPushforwardObjUnit i'.toRingCatSheafHom from
        (adji'.homEquiv _ _).apply_symm_apply _]
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  have hs := Scheme.Hom.congr_app h U
  exact congrArg (fun k ↦ k a) hs

private theorem degreeOne (A : Presentation i)
    (d : (tensorPullback f).obj (piece i' 1) ⟶ piece i 1)
    (hd : PieceFormula i i' g f h 1 d) :
    d = Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2) := by
  let e : (tensorPullback f).obj (piece i' 1) ⟶ piece i 1 :=
    Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2)
  have hcan : ∀ (U : X.affineOpens) (U' : X'.affineOpens)
      (H : U.1 ≤ g ⁻¹ᵁ U'.1) (a : (power i' 1).val.obj (op U'.1)),
      ∃ b : (power i 1).val.obj (op U.1),
        (powerInclusion i 1).app U.1 b =
          g.appLE U'.1 U.1 H ((powerInclusion i' 1).app U'.1 a) ∧
        (piece i 1).val.map (homOfLE (i.preimage_mono H)).op
          ((adjointPiece i i' g f h 1 e).val.app (op U'.1) a) =
            representative i 1 U.1 b :=
    (Classical.choose_spec ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2)).1.2
  apply pieceFormula_unique i i' g f h A 1 d e hd
  intro U U' H a r
  obtain ⟨b, hb, hcb⟩ := hcan U U' H a
  refine ⟨r • b, ?_, ?_⟩
  · change (powerInclusion i 1).app U.1 (r • b) = _
    rw [Hom.app_smul]
    change r * (@id Γ(X, U.1) ((powerInclusion i 1).app U.1 b)) = _
    rw [show (powerInclusion i 1).app U.1 b = _ from hb]
    exact mul_comm _ _
  · rw [representative_smul]
    exact congrArg (fun t ↦ i.app U.1 r • t) hcb

private theorem normalizedPieceComparison (hc : IsLimit (PullbackCone.mk i f h))
    (A : Presentation i) (A' : Presentation i') :
    ∃ d : ∀ n, (tensorPullback f).obj (piece i' n) ⟶ piece i n,
      (∀ n, PieceFormula i i' g f h n (d n)) ∧
      (∀ n, Epi (d n)) ∧ (Flat g → ∀ n, IsIso (d n)) ∧
      (d 0 ≫ tensorPullbackObjUnitToUnit i =
        (tensorPullback f).map (tensorPullbackObjUnitToUnit i') ≫
          tensorPullbackObjUnitToUnit f) ∧
      d 1 = Classical.choose ((Classical.choose_spec
        (closedImmersion_conormal_functorial i i' g f h).2).2) := by
  classical
  choose γ hγ hepi hiso using fun n ↦ powerComparison i i' g f h hc A A' n
  choose d hd hdepi hdiso using fun n ↦ pieceComparisonOfPower i i' g f h n (γ n)
  have hformula (n : ℕ) :=
    pieceFormula_of_powerComparison i i' g f h n (γ n) (hγ n) (d n) (hd n)
  exact ⟨d, hformula, fun n ↦ hdepi n (hepi n), fun hg n ↦ hdiso n (hiso n hg),
    degreeZeroOfPower i i' g f h (γ 0) (hγ 0) (d 0) (hd 0),
    degreeOne i i' g f h A (d 1) (hformula 1)⟩

private theorem cofanComparison {C : Type*} [Category C]
    {S T : ℕ → C} {M N : C} {a : ∀ n, S n ⟶ M} {b : ∀ n, T n ⟶ N}
    (L : IsColimit (Cofan.mk M a)) (R : IsColimit (Cofan.mk N b))
    (d : ∀ n, S n ⟶ T n) :
    ∃ c : M ⟶ N, (∀ n, a n ≫ c = d n ≫ b n) ∧
      ((∀ n, Epi (d n)) → Epi c) ∧ ((∀ n, IsIso (d n)) → IsIso c) := by
  let c := Cofan.IsColimit.desc L (fun n ↦ d n ≫ b n)
  have hc (n : ℕ) : a n ≫ c = d n ≫ b n := Cofan.IsColimit.fac L _ n
  refine ⟨c, hc, ?_, ?_⟩
  · intro hd
    constructor
    intro P x y hxy
    apply Cofan.IsColimit.hom_ext R
    intro n
    have := hd n
    change b n ≫ x = b n ≫ y
    apply (cancel_epi (d n)).mp
    rw [← Category.assoc, ← Category.assoc, ← hc, Category.assoc, Category.assoc, hxy]
  · intro hd
    let (n : ℕ) := hd n
    let q := Cofan.IsColimit.desc R (fun n ↦ inv (d n) ≫ a n)
    have hq (n : ℕ) : b n ≫ q = inv (d n) ≫ a n :=
      Cofan.IsColimit.fac R _ n
    refine ⟨⟨q, ?_, ?_⟩⟩
    · apply Cofan.IsColimit.hom_ext L
      intro n
      change a n ≫ (c ≫ q) = a n ≫ 𝟙 _
      rw [← Category.assoc, hc, Category.assoc, hq]
      simp
    · apply Cofan.IsColimit.hom_ext R
      intro n
      change b n ≫ (q ≫ c) = b n ≫ 𝟙 _
      rw [← Category.assoc, hq, Category.assoc, hc]
      simp

private theorem coproductComparison (A : Presentation i) (A' : Presentation i')
    (d : ∀ n, (tensorPullback f).obj (piece i' n) ⟶ piece i n) :
    ∃ c : (tensorPullback f).obj A'.algebra.toModule ⟶ A.algebra.toModule,
      (∀ n, (tensorPullback f).map (A'.inclusion n) ≫ c = d n ≫ A.inclusion n) ∧
      ((∀ n, Epi (d n)) → Epi c) ∧ ((∀ n, IsIso (d n)) → IsIso c) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction f)
  let := adj.isLeftAdjoint
  let L := isColimitCofanMkObjOfIsColimit (tensorPullback f) (piece i')
    A'.inclusion A'.coproduct
  exact cofanComparison L A.coproduct d

private theorem baseChangeMap_unique (A : Presentation i) (A' : Presentation i')
    (c e : (tensorPullback f).obj A'.algebra.toModule ⟶ A.algebra.toModule)
    (hc : IsBaseChangeMap i i' g f h A A' c)
    (he : IsBaseChangeMap i i' g f h A A' e) : c = e := by
  obtain ⟨ρ, d, _, _, hd, hfd, _, _⟩ := hc
  obtain ⟨σ, k, _, _, hk, hfk, _, _⟩ := he
  let adj := Classical.choose (exists_tensorPullbackAdjunction f)
  let := adj.isLeftAdjoint
  apply Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
    (tensorPullback f) (piece i') A'.inclusion A'.coproduct)
  intro n
  change (tensorPullback f).map (A'.inclusion n) ≫ c =
    (tensorPullback f).map (A'.inclusion n) ≫ e
  rw [hd, hk, pieceFormula_unique i i' g f h A n (d n) (k n)
    (fun U U' H a r ↦ hfd U U' H n a r) (fun U U' H a r ↦ hfk U U' H n a r)]

private theorem restriction_comp {Y : Scheme.{u}} (M : Y.Modules)
    {U V W : Y.Opens} (a : U ⟶ V) (b : V ⟶ W) (c : U ⟶ W)
    (t : M.presheaf.obj (op W)) :
    M.presheaf.map c.op t = M.presheaf.map a.op (M.presheaf.map b.op t) := by
  have hc : c = a ≫ b := Subsingleton.elim _ _
  rw [hc, op_comp, Functor.map_comp]
  rfl

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
private theorem adjoint_homogeneous_square
    (M' : Z'.Modules) (M : Z.Modules) (n : ℕ)
    (p' : piece i' n ⟶ M') (p : piece i n ⟶ M)
    (c : (tensorPullback f).obj M' ⟶ M)
    (d : (tensorPullback f).obj (piece i' n) ⟶ piece i n)
    (hc : (tensorPullback f).map p' ≫ c = d ≫ p)
    (U : X.Opens) (U' : X'.Opens) (H : U ≤ g ⁻¹ᵁ U')
    (Hf : i ⁻¹ᵁ U ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'))
    (a : (power i' n).val.obj (op U')) :
    M.presheaf.map (homOfLE Hf).op
      ((((Classical.choose (exists_tensorPullbackAdjunction f)).homEquiv _ _ c).app
        (i' ⁻¹ᵁ U') (p'.app (i' ⁻¹ᵁ U') (representative i' n U' a)))) =
    p.app (i ⁻¹ᵁ U) ((piece i n).presheaf.map
      (homOfLE (i.preimage_mono H)).op
        ((adjointPiece i i' g f h n d).app U' a)) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction f)
  let q := adj.homEquiv _ _ c
  have hq : p' ≫ q = adj.homEquiv _ _ d ≫ (pushforward f).map p := by
    rw [← Adjunction.homEquiv_naturality_left, hc,
      Adjunction.homEquiv_naturality_right]
  have hsec : q.app (i' ⁻¹ᵁ U') (p'.app _ (representative i' n U' a)) =
      p.app (f ⁻¹ᵁ (i' ⁻¹ᵁ U'))
        ((adj.homEquiv _ _ d).app (i' ⁻¹ᵁ U') (representative i' n U' a)) :=
    congrArg (fun k : piece i' n ⟶ (pushforward f).obj M ↦
      k.app (i' ⁻¹ᵁ U') (representative i' n U' a)) hq
  change M.presheaf.map _ (q.app _ (p'.app _ _)) = _
  rw [hsec]
  refine (Hom.app_presheaf_map p (homOfLE Hf)
    ((adj.homEquiv _ _ d).app (i' ⁻¹ᵁ U') (representative i' n U' a))).symm.trans ?_
  apply congrArg (p.app (i ⁻¹ᵁ U))
  let t : (piece i n).presheaf.obj (op (f ⁻¹ᵁ (i' ⁻¹ᵁ U'))) :=
    (adj.homEquiv _ _ d).app (i' ⁻¹ᵁ U') (representative i' n U' a)
  have E : (i ≫ g) ⁻¹ᵁ U' = f ⁻¹ᵁ (i' ⁻¹ᵁ U') :=
    congrArg (fun k : Z ⟶ X' ↦ k ⁻¹ᵁ U') h
  change (piece i n).presheaf.map (homOfLE Hf).op t =
    (piece i n).presheaf.map (homOfLE (i.preimage_mono H)).op
      ((piece i n).presheaf.map (eqToHom E).op t)
  exact restriction_comp (piece i n) (homOfLE (i.preimage_mono H))
    (eqToHom E) (homOfLE Hf) t

/-- The homogeneous comparisons assemble to a base-change algebra map with the
required affine formula, normalizations, epimorphism and flat isomorphism.
Source: Stacks Project, Divisors, Tags 0634 and 0635.
(blueprint: lem-pur-conormal-algebra-flat-base-change).

Proof: assemble the degreewise comparisons through the presentation coproduct.
The affine homogeneous representative formula proves the adjoint ring-sheaf laws
by direct-sum induction and local sheaf descent. The degree-zero and degree-one
normalizations are inherited from the canonical unit and conormal maps. The
coproduct map is epi when each degree map is epi; under flatness the degreewise
inverses assemble to an inverse. -/
private theorem exists_baseChangeMap_assembly (hc : IsLimit (PullbackCone.mk i f h))
    (A : Presentation i) (A' : Presentation i') :
    ∃ c : (tensorPullback f).obj A'.algebra.toModule ⟶ A.algebra.toModule,
      IsBaseChangeMap i i' g f h A A' c ∧ Epi c ∧ (Flat g → IsIso c) := by
  obtain ⟨d, hformula, hepi, hiso, hzero, hone⟩ :=
    normalizedPieceComparison i i' g f h hc A A'
  obtain ⟨c, hcgraded, hcepi, hciso⟩ := coproductComparison i i' f A A' d
  let q := (Classical.choose (exists_tensorPullbackAdjunction f)).homEquiv _ _ c
  have hq : ∀ (U : X.affineOpens) (U' : X'.affineOpens)
      (H : U.1 ≤ g ⁻¹ᵁ U'.1) (Hf : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ U'.1))
      (n : ℕ) (a : (power i' n).val.obj (op U'.1)),
      ∃ b : (power i n).val.obj (op U.1),
        (powerInclusion i n).app U.1 b =
          g.appLE U'.1 U.1 H ((powerInclusion i' n).app U'.1 a) ∧
        A.algebra.right.obj.map (homOfLE Hf).op
          (q.val.app (op (i' ⁻¹ᵁ U'.1))
            (homogeneousClass i' A'.algebra A'.inclusion n U'.1 a)) =
          homogeneousClass i A.algebra A.inclusion n U.1 b := by
    intro U U' H Hf n a
    obtain ⟨b, hb, hdb⟩ := hformula n U U' H a 1
    refine ⟨b, ?_, ?_⟩
    · change (powerInclusion i n).val.app (op U.1) b =
        g.appLE U'.1 U.1 H ((powerInclusion i' n).val.app (op U'.1) a)
      simpa only [mul_one] using hb
    · have hs := adjoint_homogeneous_square i i' g f h A'.algebra.toModule
        A.algebra.toModule n (A'.inclusion n) (A.inclusion n) c (d n) (hcgraded n)
        U.1 U'.1 H Hf a
      have hb' : (piece i n).presheaf.map (homOfLE (i.preimage_mono H)).op
          ((adjointPiece i i' g f h n (d n)).app U'.1 a) =
          representative i n U.1 b := by
        change i.app U.1 1 •
          ((piece i n).presheaf.map (homOfLE (i.preimage_mono H)).op
            ((adjointPiece i i' g f h n (d n)).app U'.1 a)) =
          representative i n U.1 b at hdb
        rw [map_one, one_smul] at hdb
        exact hdb
      exact hs.trans (congrArg ((A.inclusion n).app (i ⁻¹ᵁ U.1)) hb')
  obtain ⟨ρ, hρ, hρq⟩ := exists_ringAdjoint_of_homogeneousFormula
    i i' g f h A A' q hq
  refine ⟨c, ?_, hcepi hepi, fun hg ↦ hciso (hiso hg)⟩
  refine ⟨ρ, d, hρ, ?_, hcgraded,
    fun U U' H n a r ↦ hformula n U U' H a r, hzero, hone⟩
  intro V a
  exact hρq V a

/-- The canonical comparison of conormal graded algebras exists uniquely. Its underlying
module map is an epimorphism, and it is an isomorphism when the ambient base change is flat.
Source: Stacks Project, Divisors, Tags 0634 and 0635
(blueprint: lem-pur-conormal-algebra-flat-base-change). -/
theorem existsUnique_baseChangeMap (hc : IsLimit (PullbackCone.mk i f h))
    (A : Presentation i) (A' : Presentation i') :
    (∀ (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1),
      i.ker.ideal U = Ideal.map (g.appLE U'.1 U.1 H).hom (i'.ker.ideal U')) ∧
    (∃! c : (tensorPullback f).obj A'.algebra.toModule ⟶ A.algebra.toModule,
      IsBaseChangeMap i i' g f h A A' c) ∧
    ∀ c : (tensorPullback f).obj A'.algebra.toModule ⟶ A.algebra.toModule,
      IsBaseChangeMap i i' g f h A A' c → Epi c ∧ (Flat g → IsIso c) := by
  obtain ⟨c, hC, he, hf⟩ := exists_baseChangeMap_assembly i i' g f h hc A A'
  refine ⟨?_, ⟨c, hC, ?_⟩, ?_⟩
  · intro U U' H
    rw [baseChangeIdeal i i' g f h hc]
    exact Scheme.IdealSheafData.ideal_comap_appLE i'.ker g U' U H
  · intro e he'
    exact baseChangeMap_unique i i' g f h A A' e c he' hC
  · intro e he'
    have heq := baseChangeMap_unique i i' g f h A A' e c he' hC
    subst e
    exact ⟨he, fun hg ↦ hf hg⟩

end AlgebraicGeometry.ConormalGradedAlgebra
