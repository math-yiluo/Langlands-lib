import Langlands.Geometry.Building.TwistedFixedTranslationLattice
import Langlands.Geometry.Building.TwistedFixedTranslationCentralizer
import Langlands.GroupScheme.Absolute.InfiniteGaloisCocharacterDescent
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Twisted-fixed cocharacters come from the split torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.TwistedFixedTranslationSplitDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {iS : S.toGrp ⟶ G} (iT : T.toGrp ⟶ G)
  {f : S ⟶ T}

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) iT
local notation "iS_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) iS

/-- The base change of `iS = f ≫ iT` is `f_K ≫ i_K`. -/
theorem baseChange_iS_eq (hf : CommGroupScheme.groupHom f ≫ iT = iS) :
    iS_K = CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map f) ≫ i_K := by
  rw [← hf, Functor.map_comp]
  rfl

/-- Over `K`, the values of the conjugated cocharacter `λ ≫ i_K ≫ Int(h)` commute with the
values of `iS_K`, provided conjugation by `h` fixes `iS_K`: both factor through the
commutative group `T_K` followed by `i_K ≫ Int(h)`. -/
theorem commute_conj_values (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (h : rationalPoints G_K) (hA : iS_K ≫ ((G_K).innerIso h).hom = iS_K)
    (lam : cocharacterLattice T_K) {U : Over (Spec (CommRingCat.of K))}
    (x : U ⟶ (Gm (Spec (CommRingCat.of K))).X) (y : U ⟶ (S_K).X) :
    Commute (x ≫ (CommGroupScheme.groupHom lam ≫ i_K ≫ ((G_K).innerIso h).hom).hom.hom)
      (y ≫ (iS_K).hom.hom) := by
  have hy : iS_K = CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map f) ≫
      i_K ≫ ((G_K).innerIso h).hom := by
    rw [← hA, baseChange_iS_eq k K iT hf, Category.assoc]
  rw [hy]
  have hc : Commute (x ≫ (CommGroupScheme.groupHom lam).hom.hom)
      (y ≫ (CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map f)).hom.hom) :=
    Commute.all _ _
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [Commute, SemiconjBy, ← MonObj.mul_comp, ← MonObj.mul_comp, hc.eq, MonObj.mul_comp,
    MonObj.mul_comp]

variable [IsGalois k K] [IsAffineHom G.X.hom]

/-- The cocharacter of `G` descended from `λ ≫ i_K ≫ Int(h)` commutes with `iS` on every
test scheme over `k`. -/
theorem commute_descend_values (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (h : rationalPoints G_K) (hA : iS_K ≫ ((G_K).innerIso h).hom = iS_K)
    (lam : cocharacterLattice T_K)
    (hinv : GaloisCocharacterDescent.IsInvariant k K G
      (CommGroupScheme.groupHom lam ≫ i_K ≫ ((G_K).innerIso h).hom))
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ (Gm (Spec (CommRingCat.of k))).X)
    (y : U ⟶ S.X) :
    Commute (x ≫ (InfiniteGaloisCocharacterDescent.descend k K G _ hinv).hom.hom)
      (y ≫ iS.hom.hom) := by
  let := GaloisCocharacterDescent.faithful_algebraPullback k K
  have hd := InfiniteGaloisCocharacterDescent.baseChange_descend k K G _ hinv
  rw [Iso.inv_comp_eq] at hd
  have e1 : (Over.pullback b).map
      (x ≫ (InfiniteGaloisCocharacterDescent.descend k K G _ hinv).hom.hom) =
      ((Over.pullback b).map x ≫ (Gm.baseChangeIso b).hom.hom.hom) ≫
        (CommGroupScheme.groupHom lam ≫ i_K ≫ ((G_K).innerIso h).hom).hom.hom := by
    rw [Functor.map_comp, Category.assoc]
    exact congrArg (fun q => (Over.pullback b).map x ≫ q.hom.hom) hd
  have e2 : (Over.pullback b).map (y ≫ iS.hom.hom) =
      (Over.pullback b).map y ≫ (iS_K).hom.hom := by
    rw [Functor.map_comp]
    rfl
  apply (Over.pullback b).map_injective
  rw [Functor.map_mul, Functor.map_mul, e1, e2]
  exact (commute_conj_values k K iT hf h hA lam _ _).eq

variable [Infinite K]
  [Mono (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) iT).hom.hom.left]

/-- **Twisted-fixed cocharacters come from `S_K`.** Let `iS : S → G` be a maximal split torus
over `k`, `f : S → T` with `f ≫ iT = iS`, and `K / k` Galois with `K` infinite. Let `h ∈ G(K)`
commute with `iS(S(K))` and let `n σ = h⁻¹ σ(h)` normalize `T_K`. Every cocharacter `λ` of
`T_K` with `σ(λ) · n_σ = λ` for all `σ` is `ν ≫ f_K` for a cocharacter `ν` of `S_K`. -/
theorem exists_split_of_twisted_fixed (hS : IsMaximalSplitTorus iS)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (h : rationalPoints G_K)
    (hh : ∀ s : rationalPoints (baseChanged k K S.toGrp),
      Commute h (rationalPoints.map ((GroupScheme.baseChange (baseMap k K)).map iS) s))
    (n : (K ≃ₐ[k] K) → normalizerPoints (T := T_K) i_K)
    (hn : ∀ σ, (n σ : rationalPoints G_K) = h⁻¹ * rationalConjugate k K G σ h)
    (lam : cocharacterLattice T_K)
    (hlam : ∀ σ, cocharacterLattice.galoisRepresentation k K T σ lam ≫
      (normalizingAut (T := T_K) i_K (n σ)).hom = lam) :
    ∃ ν : cocharacterLattice S_K, ν ≫ (CommGroupScheme.baseChange b).map f = lam := by
  have hinv := TwistedFixedTranslation.isInvariant_conj_of_twisted_fixed k K iT h n hn lam hlam
  have hSK : IsSplitTorus (S_K).toGrp := hS.1.1.baseChange b
  have hA := TwistedFixedTranslationCentralizer.comp_innerIso_eq_of_commute iS hSK h hh
  obtain ⟨νF, hνF⟩ := hS.exists_factor_of_commute isSplitTorus_gm
    (InfiniteGaloisCocharacterDescent.descend k K G _ hinv)
    (fun U x y => commute_descend_values k K iT hf h hA lam hinv U x y)
  refine ⟨Additive.ofMul ((Gm.baseChangeIso b).inv ≫ (GroupScheme.baseChange b).map νF), ?_⟩
  have key : ((Gm.baseChangeIso b).inv ≫ (GroupScheme.baseChange b).map νF) ≫
      CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map f) ≫ i_K ≫
        ((G_K).innerIso h).hom =
      CommGroupScheme.groupHom lam ≫ i_K ≫ ((G_K).innerIso h).hom := by
    rw [← Category.assoc (CommGroupScheme.groupHom _), ← baseChange_iS_eq k K iT hf, hA,
      Category.assoc, ← Functor.map_comp, hνF]
    exact InfiniteGaloisCocharacterDescent.baseChange_descend k K G _ hinv
  simp only [← Category.assoc] at key
  have key' := (cancel_mono ((G_K).innerIso h).hom).mp key
  have : Mono (i_K).hom.hom := Over.mono_of_mono_left _
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact (cancel_mono (i_K).hom.hom).mp (congrArg (fun q => q.hom.hom) key')

end Langlands.Geometry.Building.TwistedFixedTranslationSplitDescent
