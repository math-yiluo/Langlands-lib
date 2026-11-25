/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
/-!
# Finite Tate sheaves and inverse image
Source: Stacks Project, Etale Cohomology, Tags 03PK and 03Q1; Modules on Sites,
Tags 03EK and 03EM; Cohomology on Sites, Tags 07A4 and 0G7E
(auxiliary; not a blueprint node).
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme
set_option synthInstance.maxSize 2048 in
/-- Finite Tate sheaves are locally free lines, with the normalized inverse-image
comparisons, their signed tensor products, and exponent-change comparisons.
Source: Stacks Project, Tags 03PK, 03Q1, 03EK, 03EM, 07A4 and 0G7E
(auxiliary; not a blueprint node).
Proof plan:
1. Apply `lem-asd-finite-etale-twist-line` to `ℤ/m` to trivialize the roots sheaf.
   Extend its cyclic basis to `A`. This uses only `m A = 0`, not finiteness or flatness
   of `A`. Tensor powers and the dual basis trivialize all signed powers on this cover.
2. Over an affine open represent `μ_m` by `Spec R[t]/(t^m-1)`. The root-splitting
   etaleness lemma makes this an object of the small etale site. The representable
   inverse-image and Yoneda lemmas identify its pullback with the same root functor.
   The adjunct sends each root to its restriction along the base-change projection.
3. Glue these affine comparisons using etale-cover detection of isomorphisms.
   The algebraic-structures and composition-unit lemmas identify the abelian
   adjuncts. Restriction preserves powers, giving the displayed normalization.
4. The left-exact site inverse-image tensor lemma and exact module inverse image
   preserve coefficient extension and positive powers. On pure tensors the map
   sends `a ⊗ z` to `a ⊗ v⁻¹z`, which is the generator equation below.
5. Pull back evaluation. On a local basis and its dual the comparison preserves
   evaluation and is invertible. This determines every negative comparison.
6. Concatenation and contraction on signed basis tensors give the product maps.
   Changes of basis multiply degree `a` by `u^a`, so the maps glue and satisfy
   associativity, symmetry, units, evaluation, identities, and composition.
7. Exact inverse image is its own left derived functor. The ringed-topos derived
   tensor comparison, computed on K-flat flat-term resolutions, gives the natural
   unbounded derived comparison; additive inverse image preserves shift signs.
   The derived comparison is the composite of these canonical maps, so its tensor
   and composition compatibilities follow termwise from those of steps 3--6.
8. For `m' = q m`, choose a local primitive `m'`-root `ζ`. Its power `ζ^q`
   trivializes `μ_m`. The power map is reduction in these bases and induces the
   identity on `A` after scalar extension. Tensor powers and inverse duals give
   all exponent-change comparisons. Power maps commute with pullback and compose.
-/
theorem etaleFiniteTwistPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) :
    ∃ (r : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) →
        ((Etale.upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf m) ≅
          T'.rootsOfUnitySheaf m))
      (c : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) → IsUnit (m : Γ(T', ⊤)) → ∀ a : ℤ,
        (Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateSheaf A m T hA a) ≅
          finiteEtaleTateSheaf A m T' hA a)
      (p : ∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) → ∀ a b : ℤ,
        finiteEtaleTateSheaf A m T hA a ⊗ finiteEtaleTateSheaf A m T hA b ≅
          finiteEtaleTateSheaf A m T hA (a + b)),
    (∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) →
      ∃ U : Cover.{u} etalePrecoverage T, ∀ (i : U.I₀) (a : ℤ),
        Nonempty ((finiteEtaleTateSheaf A m T hA a).over (U.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (U.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))),
      (Etale.upperStar AddCommGrpCat.{u + 1} v).map (kernel.ι (m • 𝟙 T.gmSheaf)) ≫
          upperStarGmSheafToGmSheaf v =
        (r v hT).hom ≫ kernel.ι (m • 𝟙 T'.gmSheaf)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (W : T.Etaleᵒᵖ) (a : A)
        (z : (T.rootsOfUnitySheaf m).obj.obj W),
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
        (c v hT hT' 1).hom).hom.app W (finiteEtaleTateOneGenerator A m T hA W a z) =
      finiteEtaleTateOneGenerator A m T' hA
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) a
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          (r v hT).hom).hom.app W z)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))),
      c v hT hT' 0 = (upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
        (ModuleCat.of A A)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      c v hT hT' (.ofNat (n + 2)) =
        asIso (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1))) (finiteEtaleTateLine T m A hA)) ≪≫
          tensorIso (c v hT hT' (.ofNat (n + 1))) (c v hT hT' 1)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map
          ((ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T hA 0)) ≫ (c v hT hT' 0).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))
          (finiteEtaleTateSheaf A m T hA (.negSucc n)) ≫
          tensorHom (c v hT hT' (.ofNat (n + 1))).hom (c v hT hT' (.negSucc n)).hom ≫
          (ihom.ev (finiteEtaleTateSheaf A m T' hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T' hA 0)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      c (𝟙 T) hT hT a = (Etale.upperStarId (ModuleCat.{u + 1} A) T).app
        (finiteEtaleTateSheaf A m T hA a)) ∧
    (∀ {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
        (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤)))
        (hT'' : IsUnit (m : Γ(T'', ⊤))) (a : ℤ),
      c (w ≫ v) hT hT'' a =
        (Etale.upperStarComp (ModuleCat.{u + 1} A) w v).app
          (finiteEtaleTateSheaf A m T hA a) ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} A) w).mapIso (c v hT hT' a) ≪≫
          c w hT' hT'' a) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT 0 a = λ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (zero_add a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT a 0 = ρ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (add_zero a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      p T hT (.ofNat (n + 1)) 1 = Iso.refl _) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b d : ℤ),
      (p T hT a b).hom ▷ finiteEtaleTateSheaf A m T hA d ≫ (p T hT (a + b) d).hom =
        (α_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)
          (finiteEtaleTateSheaf A m T hA d)).hom ≫
        finiteEtaleTateSheaf A m T hA a ◁ (p T hT b d).hom ≫
          (p T hT a (b + d)).hom ≫
            eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_assoc a b d).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b : ℤ),
      (β_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)).hom ≫
          (p T hT b a).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_comm b a)) =
        (p T hT a b).hom) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      (p T hT (.ofNat (n + 1)) (.negSucc n)).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA)
            (add_neg_cancel (Int.ofNat (n + 1)))) =
        (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
          (finiteEtaleTateSheaf A m T hA 0)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map (p T hT a b).hom ≫
          (c v hT hT' (a + b)).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b) ≫
        tensorHom (c v hT hT' a).hom (c v hT hT' b).hom ≫ (p T' hT' a b).hom) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      ∃ d : ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) T
          ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)) ⋙
          shiftFunctor _ b) ⋙ (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ≅
        (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ⋙
          Etale.derivedTensorRight (ModuleCat.{u + 1} A) T'
            ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T' hA a)) ⋙
              shiftFunctor _ b),
        ∀ K : Etale.DerivedCategoryModule A T,
          d.app K =
            ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.commShiftIso b).app
              (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj
                ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a))) ≪≫
            (shiftFunctor _ b).mapIso
              (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v K
                ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)) ≪≫
              ((Etale.derivedTensor (ModuleCat.{u + 1} A) T').obj
                ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K)).mapIso
                ((Etale.singleFunctorCompLeftDerivedUpperStarIso
                  (ModuleCat.{u + 1} A) v).app (finiteEtaleTateSheaf A m T hA a) ≪≫
                (DerivedCategory.singleFunctor _ 0).mapIso (c v hT hT' a)))) ∧
    (∀ (m' : ℕ), 0 < m' → ∀ (hdiv : m ∣ m')
        (T : Scheme.{u}),
      IsUnit (m' : Γ(T, ⊤)) →
      ∃ (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
        (t : ∀ a : ℤ, finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) a ≅
          finiteEtaleTateSheaf A m T hA a),
      q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf) ∧
      (∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m').obj.obj W),
        (t 1).hom.hom.app W (finiteEtaleTateOneGenerator A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) W a z) =
          finiteEtaleTateOneGenerator A m T hA W a (q.hom.app W z)) ∧
      t 0 = Iso.refl _ ∧
      (∀ n : ℕ, t (.ofNat (n + 2)) =
        tensorIso (t (.ofNat (n + 1))) (t 1)) ∧
      (∀ n : ℕ,
        tensorHom (t (.ofNat (n + 1))).hom (t (.negSucc n)).hom ≫
            (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
              (finiteEtaleTateSheaf A m T hA 0) =
          (ihom.ev (finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv))
            (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) 0))) := by
  obtain ⟨r, c, p, hbase⟩ := etaleFiniteTwistPullback_base A m hm hA
  obtain hrest := etaleFiniteTwistPullback_rest A m hm hA r c p
  let hh := @And.intro _ _ hbase hrest
  refine ⟨r, c, p, ?_⟩
  simpa only [and_assoc] using hh

/-! ## Structured normalized comparisons

Source: Stacks Project, Tags 03PK, 03Q1, 03EK, 03EM, 07A4 and 0G7E
(auxiliary; not a blueprint node).

Named projections expose the same three witnesses and every law of the theorem above.
The original declaration remains unchanged for existing consumers.
-/

noncomputable section StructuredComparisons

set_option autoImplicit false
set_option synthInstance.maxSize 2048

/-- The root, signed pullback and signed multiplication maps with every normalization of
etaleFiniteTwistPullback, including unbounded derived pullback and exponent change.
Source: Stacks 03PK, 03Q1, 03EK, 03EM, 07A4 and 0G7E
(auxiliary; not a blueprint node). -/
structure FiniteEtaleTwistPullbackData (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) where
  /-- Roots of unity, normalized by their inclusion in G_m. -/
  r : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) →
        ((Etale.upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf m) ≅
          T'.rootsOfUnitySheaf m)
  /-- Signed inverse-image comparisons. -/
  c : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) → IsUnit (m : Γ(T', ⊤)) → ∀ a : ℤ,
        (Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateSheaf A m T hA a) ≅
          finiteEtaleTateSheaf A m T' hA a
  /-- Signed Tate multiplication. -/
  p : ∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) → ∀ a b : ℤ,
        finiteEtaleTateSheaf A m T hA a ⊗ finiteEtaleTateSheaf A m T hA b ≅
          finiteEtaleTateSheaf A m T hA (a + b)
  /-- All the original normalization and compatibility laws, without omissions. -/
  laws :
    (∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) →
      ∃ U : Cover.{u} etalePrecoverage T, ∀ (i : U.I₀) (a : ℤ),
        Nonempty ((finiteEtaleTateSheaf A m T hA a).over (U.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (U.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤))),
      (Etale.upperStar AddCommGrpCat.{u + 1} v).map (kernel.ι (m • 𝟙 T.gmSheaf)) ≫
          upperStarGmSheafToGmSheaf v =
        (r v hT).hom ≫ kernel.ι (m • 𝟙 T'.gmSheaf)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (W : T.Etaleᵒᵖ) (a : A)
        (z : (T.rootsOfUnitySheaf m).obj.obj W),
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
        (c v hT hT' 1).hom).hom.app W (finiteEtaleTateOneGenerator A m T hA W a z) =
      finiteEtaleTateOneGenerator A m T' hA
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) a
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          (r v hT).hom).hom.app W z)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))),
      c v hT hT' 0 = (upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
        (ModuleCat.of A A)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      c v hT hT' (.ofNat (n + 2)) =
        asIso (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1))) (finiteEtaleTateLine T m A hA)) ≪≫
          tensorIso (c v hT hT' (.ofNat (n + 1))) (c v hT hT' 1)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (n : ℕ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map
          ((ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T hA 0)) ≫ (c v hT hT' 0).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))
          (finiteEtaleTateSheaf A m T hA (.negSucc n)) ≫
          tensorHom (c v hT hT' (.ofNat (n + 1))).hom (c v hT hT' (.negSucc n)).hom ≫
          (ihom.ev (finiteEtaleTateSheaf A m T' hA (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m T' hA 0)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      c (𝟙 T) hT hT a = (Etale.upperStarId (ModuleCat.{u + 1} A) T).app
        (finiteEtaleTateSheaf A m T hA a)) ∧
    (∀ {T T' T'' : Scheme.{u}} (v : T' ⟶ T) (w : T'' ⟶ T')
        (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤)))
        (hT'' : IsUnit (m : Γ(T'', ⊤))) (a : ℤ),
      c (w ≫ v) hT hT'' a =
        (Etale.upperStarComp (ModuleCat.{u + 1} A) w v).app
          (finiteEtaleTateSheaf A m T hA a) ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} A) w).mapIso (c v hT hT' a) ≪≫
          c w hT' hT'' a) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT 0 a = λ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (zero_add a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a : ℤ),
      p T hT a 0 = ρ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (add_zero a).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      p T hT (.ofNat (n + 1)) 1 = Iso.refl _) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b d : ℤ),
      (p T hT a b).hom ▷ finiteEtaleTateSheaf A m T hA d ≫ (p T hT (a + b) d).hom =
        (α_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)
          (finiteEtaleTateSheaf A m T hA d)).hom ≫
        finiteEtaleTateSheaf A m T hA a ◁ (p T hT b d).hom ≫
          (p T hT a (b + d)).hom ≫
            eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_assoc a b d).symm)) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (a b : ℤ),
      (β_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)).hom ≫
          (p T hT b a).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_comm b a)) =
        (p T hT a b).hom) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) (n : ℕ),
      (p T hT (.ofNat (n + 1)) (.negSucc n)).hom ≫
          eqToHom (congrArg (finiteEtaleTateSheaf A m T hA)
            (add_neg_cancel (Int.ofNat (n + 1)))) =
        (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
          (finiteEtaleTateSheaf A m T hA 0)) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      (Etale.upperStar (ModuleCat.{u + 1} A) v).map (p T hT a b).hom ≫
          (c v hT hT' (a + b)).hom =
        Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
          (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b) ≫
        tensorHom (c v hT hT' a).hom (c v hT hT' b).hom ≫ (p T' hT' a b).hom) ∧
    (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      ∃ d : ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) T
          ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)) ⋙
          shiftFunctor _ b) ⋙ (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ≅
        (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ⋙
          Etale.derivedTensorRight (ModuleCat.{u + 1} A) T'
            ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T' hA a)) ⋙
              shiftFunctor _ b),
        ∀ K : Etale.DerivedCategoryModule A T,
          d.app K =
            ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.commShiftIso b).app
              (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj
                ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a))) ≪≫
            (shiftFunctor _ b).mapIso
              (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v K
                ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)) ≪≫
              ((Etale.derivedTensor (ModuleCat.{u + 1} A) T').obj
                ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K)).mapIso
                ((Etale.singleFunctorCompLeftDerivedUpperStarIso
                  (ModuleCat.{u + 1} A) v).app (finiteEtaleTateSheaf A m T hA a) ≪≫
                (DerivedCategory.singleFunctor _ 0).mapIso (c v hT hT' a)))) ∧
    (∀ (m' : ℕ), 0 < m' → ∀ (hdiv : m ∣ m')
        (T : Scheme.{u}),
      IsUnit (m' : Γ(T, ⊤)) →
      ∃ (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
        (t : ∀ a : ℤ, finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) a ≅
          finiteEtaleTateSheaf A m T hA a),
      q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf) ∧
      (∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m').obj.obj W),
        (t 1).hom.hom.app W (finiteEtaleTateOneGenerator A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) W a z) =
          finiteEtaleTateOneGenerator A m T hA W a (q.hom.app W z)) ∧
      t 0 = Iso.refl _ ∧
      (∀ n : ℕ, t (.ofNat (n + 2)) =
        tensorIso (t (.ofNat (n + 1))) (t 1)) ∧
      (∀ n : ℕ,
        tensorHom (t (.ofNat (n + 1))).hom (t (.negSucc n)).hom ≫
            (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
              (finiteEtaleTateSheaf A m T hA 0) =
          (ihom.ev (finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv))
            (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) 0)))

/-- The structured finite Tate comparisons exist, with the normalized inverse-image
comparisons, their signed tensor products, and exponent-change comparisons.
Source: Stacks Project, Tags 03PK, 03Q1, 03EK, 03EM, 07A4 and 0G7E
(auxiliary; not a blueprint node).
Proof plan:
1. Apply `lem-asd-finite-etale-twist-line` to `ℤ/m` to trivialize the roots sheaf.
   Extend its cyclic basis to `A`. This uses only `m A = 0`, not finiteness or flatness
   of `A`. Tensor powers and the dual basis trivialize all signed powers on this cover.
2. Over an affine open represent `μ_m` by `Spec R[t]/(t^m-1)`. The root-splitting
   etaleness lemma makes this an object of the small etale site. The representable
   inverse-image and Yoneda lemmas identify its pullback with the same root functor.
   The adjunct sends each root to its restriction along the base-change projection.
3. Glue these affine comparisons using etale-cover detection of isomorphisms.
   The algebraic-structures and composition-unit lemmas identify the abelian
   adjuncts. Restriction preserves powers, giving the displayed normalization.
4. The left-exact site inverse-image tensor lemma and exact module inverse image
   preserve coefficient extension and positive powers. On pure tensors the map
   sends `a ⊗ z` to `a ⊗ v⁻¹z`, which is the generator equation below.
5. Pull back evaluation. On a local basis and its dual the comparison preserves
   evaluation and is invertible. This determines every negative comparison.
6. Concatenation and contraction on signed basis tensors give the product maps.
   Changes of basis multiply degree `a` by `u^a`, so the maps glue and satisfy
   associativity, symmetry, units, evaluation, identities, and composition.
7. Exact inverse image is its own left derived functor. The ringed-topos derived
   tensor comparison, computed on K-flat flat-term resolutions, gives the natural
   unbounded derived comparison; additive inverse image preserves shift signs.
   The derived comparison is the composite of these canonical maps, so its tensor
   and composition compatibilities follow termwise from those of steps 3--6.
8. For `m' = q m`, choose a local primitive `m'`-root `ζ`. Its power `ζ^q`
   trivializes `μ_m`. The power map is reduction in these bases and induces the
   identity on `A` after scalar extension. Tensor powers and inverse duals give
   all exponent-change comparisons. Power maps commute with pullback and compose.
-/
theorem nonempty_finiteEtaleTwistPullbackData (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) :
    Nonempty (FiniteEtaleTwistPullbackData A m hA) := by
  obtain ⟨r, c, p, laws⟩ := etaleFiniteTwistPullback A m hm hA
  exact ⟨⟨r, c, p, laws⟩⟩

/-- Select the normalized comparisons. Constants and pure root tensors determine c, and
unitors, positive recursion, associativity and evaluation determine p; r is determined by
its monic inclusion into G_m. Thus the data are unique up to equality, including the duals.
Source: Stacks 03PK, 03Q1, 03EK, 03EM, 07A4 and 0G7E
(auxiliary; not a blueprint node). -/
@[irreducible]
def finiteEtaleTwistPullbackData (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) : FiniteEtaleTwistPullbackData A m hA :=
  Classical.choice (nonempty_finiteEtaleTwistPullbackData A m hm hA)

end StructuredComparisons

end AlgebraicGeometry.Scheme
