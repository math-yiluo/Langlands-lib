/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackNormalization
public import WeilConjectures.Algebra.Homology.Finite.FiniteFreeDualPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackExistence
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarPullbackNaturality
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer

/-! # Pullback of the signed line scalar square

Source: blueprint main-20261015, prop-weil-twist-preserves.proof.md, first and final
sentences; Stacks Project, Modules on Sites, Tags 03EL, 0GMX and 04J0.
(blueprint: lem-pur-signed-line-scalar-pullback-square)

The structural ring maps are written as adjuncts R → u_* R' and S → u_* S'.
The pullbacks are Mathlib's actual module left adjoints, with existence supplied by
`module_pushforward_isRightAdjoint_of_universes`, hence the sheafified relative tensors.
The square is tested on the adjunction-unit images of scalar tensors. These generate
by the two adjunctions, so this is the morphism equality under canonical reassociation,
not an equality restricted to bases or to global sections. The evaluation clause likewise
specifies the transpose of pulled evaluation, precomposed by the inverse positive map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}] in
private theorem pullback_section_ext
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (M : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {N : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R')}
    (f g : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj M ⟶ N)
    (h : ∀ (V : C) (x : M.val.obj (op V)),
      f.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          M V x) =
      g.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          M V x)) : f = g := by
  let := module_pushforward_isRightAdjoint_of_universes a
  apply ((pullbackPushforwardAdjunction a).homEquiv M N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  exact h V.unop x

omit [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}] in
private theorem pullback_tensor_section_ext
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (M N : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {H : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R')}
    (f g : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj
        ((siteSheafTensorRight N).obj M) ⟶ H)
    (h : ∀ (V : C) (x : M.val.obj (op V)) (y : N.val.obj (op V)),
      f.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          ((siteSheafTensorRight N).obj M) V (siteSheafTensorTmul M N (op V) x y)) =
      g.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          ((siteSheafTensorRight N).obj M) V (siteSheafTensorTmul M N (op V) x y))) :
    f = g := by
  let := module_pushforward_isRightAdjoint_of_universes a
  apply ((pullbackPushforwardAdjunction a).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply scalarTensor_hom_ext M N
  intro V x y
  exact h V.unop x y

private theorem signedLinePullbackNormalized_unique
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (hcover : CoverPreserving J K U)
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (P Q : ∀ m : ℤ, (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj
        (signedLinePower.{u, v, w} L m) ≅ signedLinePower.{u, v, w} L' m)
    (hP : SignedLinePullbackNormalized a L L' p P)
    (hQ : SignedLinePullbackNormalized a L L' p Q) : P = Q := by
  have hpos : ∀ n : ℕ, (P (.ofNat n)).hom = (Q (.ofNat n)).hom := by
    intro n
    induction n with
    | zero =>
      apply pullback_section_ext a
      intro V r
      exact (hP.1 V r).trans (hQ.1 V r).symm
    | succ n ih =>
      cases n with
      | zero => exact hP.2.1.trans hQ.2.1.symm
      | succ n =>
        apply pullback_tensor_section_ext a (scalarTensorPower R L (n + 1)) L
        intro V x y
        have he := congrArg (fun f ↦
          siteSheafTensorTmul (scalarTensorPower R' L' (n + 1)) L' (op (U.obj V))
            (f.val.app (op (U.obj V))
              (ringedSitePullbackSection a
                (module_pushforward_isRightAdjoint_of_universes a)
                (scalarTensorPower R L (n + 1)) V x))
            (p.hom.val.app (op (U.obj V))
              (ringedSitePullbackSection a
                (module_pushforward_isRightAdjoint_of_universes a) L V y))) ih
        exact (hP.2.2.1 n V x y).trans (he.trans (hQ.2.2.1 n V x y).symm)
  funext m
  apply Iso.ext
  cases m with
  | ofNat n => exact hpos n
  | negSucc n =>
    let := module_pushforward_isRightAdjoint_of_universes a
    let (V : C) : HasSheafify (J.over V) AddCommGrpCat.{max u v w} :=
      (coefficientSheafification.{max u v, v, max u v w} (J.over V)).1
    obtain ⟨d, hd, unique⟩ := exists_pullback_pairing_transfer.{u, v, w} a hcover
      (module_pushforward_isRightAdjoint_of_universes a)
      (scalarTensorPower R L (n + 1)) (signedLinePower.{u, v, w} L (.negSucc n)) (𝟙 _)
    have hcomp :
        (P (.negSucc n)).hom ≫ homObjMap (P (.ofNat (n + 1))).hom (𝟙 (unit _)) =
        (Q (.negSucc n)).hom ≫ homObjMap (P (.ofNat (n + 1))).hom (𝟙 (unit _)) := by
      apply (unique _ ?_).trans (unique _ ?_).symm
      · intro V φ x
        exact hP.2.2.2 n V φ x
      · intro V φ x
        rw [hpos (n + 1)]
        exact hQ.2.2.2 n V φ x
    have hinv : IsIso (homObjMap (P (.ofNat (n + 1))).hom (𝟙 (unit _))) := by
      refine ⟨⟨homObjMap (P (.ofNat (n + 1))).inv (𝟙 (unit _)), ?_, ?_⟩⟩
      all_goals simp [homObjMap_comp_homObjMap, homObjMap_id]
    exact (cancel_mono _).1 hcomp

/-- Unique normalized signed pullbacks and compatibility with the scalar square in every
integer degree. Source: blueprint prop-weil-twist-preserves.proof.md, first/final sentences;
Stacks 03EL, 0GMX, 0FNY and 04J0.
(blueprint: lem-pur-signed-line-scalar-pullback-square)

Proof:
1. The inverse image and module tensor comparison give normalized tensor and unit maps.
The unit multiplies the coefficient factors and its inverse inserts 1.
2. Reassociate scalar extension across the commuting coefficient square. On generators
(x tensor y) tensor t goes to (x tensor 1) tensor b(y)t. The reverse inserts 1 and
multiplies by ι'(r'); balancing and b ι = ι' a prove they are mutual inverses.
3. Starting with the unit and p (respectively q), iterate the tensor comparison. All
positive powers remain locally free rank one by their tensor bases.
4. Apply finite_free_dual_pullback to each positive power. Compose its evaluation-defined
comparison with precomposition by the inverse positive map. The evaluation identity
follows by cancelling the positive map. The same construction gives the q-family.
5. Degree zero and one are fixed; tensor recursion forces all positive maps. Pulled
evaluation and invertibility of the positive maps force every negative map, proving
uniqueness. This is equality of sheaf Hom sections on every localized site.
6. Pullback localization identifies local and global units and carries every trivializing
cover to a trivializing cover. The slice continuity follows from cover preservation.
7. Choose a local basis e for L and its image v = c(e tensor 1) for N. Their pulled images
under p and q are compatible target bases by the assumed square. Positive recursion
and dual evaluation carry every signed basis to its corresponding target basis.
8. On these charts both scalar-square composites carry the signed generator to the same
target signed basis. Linearity gives equality on every scalar multiple; sheaf uniqueness
glues the equality. This includes zero and negative degrees and uses no flatness.
-/
theorem existsUnique_signedLineScalarPullbackSquare
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R S : Sheaf J CommRingCat.{max u v w}}
    {R' S' : Sheaf K CommRingCat.{max u v w}} (ι : R ⟶ S) (ι' : R' ⟶ S')
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (b : (sheafCompose J (forget₂ CommRingCat RingCat)).obj S ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (_hab : (sheafCompose J (forget₂ CommRingCat RingCat)).map ι ≫ b =
      a ≫ (U.sheafPushforwardContinuous RingCat J K).map
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map ι'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (N' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (_hL : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (L.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (V i))))
    (_hN : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (N.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (V i))))
    (_hL' : ∃ (I : Type u) (V : I → D), K.CoversTop V ∧
      ∀ i : I, Nonempty (L'.over (V i) ≅
        unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R').over (V i))))
    (_hN' : ∃ (I : Type u) (V : I → D), K.CoversTop V ∧
      ∀ i : I, Nonempty (N'.over (V i) ≅
        unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S').over (V i))))
    (c : changeOfRingsOfUniverses ι L ≅ N)
    (c' : changeOfRingsOfUniverses ι' L' ≅ N')
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (q : (ringedSitePullbackFunctor b
      (module_pushforward_isRightAdjoint_of_universes b)).obj N ≅ N')
    (_hc : SignedLineScalarPullbackSquare ι ι' a b L N L' N' c c' p q)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses ι (signedLinePower.{u, v, w} L m) ≅
      signedLinePower.{u, v, w} N m)
    (B' : ∀ m : ℤ, changeOfRingsOfUniverses ι' (signedLinePower.{u, v, w} L' m) ≅
      signedLinePower.{u, v, w} N' m)
    (_hB : SignedLineComparisonNormalized.{u, v, w} ι L N c B)
    (_hB' : SignedLineComparisonNormalized.{u, v, w} ι' L' N' c' B') :
    ∃! PQ :
      (∀ m : ℤ, (ringedSitePullbackFunctor a
        (module_pushforward_isRightAdjoint_of_universes a)).obj
          (signedLinePower.{u, v, w} L m) ≅ signedLinePower.{u, v, w} L' m) ×
      (∀ m : ℤ, (ringedSitePullbackFunctor b
        (module_pushforward_isRightAdjoint_of_universes b)).obj
          (signedLinePower.{u, v, w} N m) ≅ signedLinePower.{u, v, w} N' m),
      SignedLinePullbackNormalized a L L' p PQ.1 ∧
      SignedLinePullbackNormalized b N N' q PQ.2 ∧
      ∀ m : ℤ, SignedLineScalarPullbackSquare ι ι' a b
        (signedLinePower.{u, v, w} L m) (signedLinePower.{u, v, w} N m)
        (signedLinePower.{u, v, w} L' m) (signedLinePower.{u, v, w} N' m)
        (B m) (B' m) (PQ.1 m) (PQ.2 m) := by
  obtain ⟨P, hP⟩ := exists_signedLinePullbackNormalized.{u, v, w}
    _hcover a L L' _hL p
  obtain ⟨Q, hQ⟩ := exists_signedLinePullbackNormalized.{u, v, w}
    _hcover b N N' _hN q
  refine ⟨(P, Q), ⟨hP, hQ, ?_⟩, ?_⟩
  · exact signedLineScalarPullbackSquare_of_normalized.{u, v, w}
      _hcover ι ι' a b _hab L N L' N' _hL _hN _hL' _hN' c c' p q _hc
      B B' _hB _hB' P Q hP hQ
  · intro PQ hPQ
    apply Prod.ext
    · exact signedLinePullbackNormalized_unique.{u, v, w}
        _hcover a L L' p PQ.1 P hPQ.1 hP
    · exact signedLinePullbackNormalized_unique.{u, v, w}
        _hcover b N N' q PQ.2 Q hPQ.2.1 hQ

end SheafOfModules
