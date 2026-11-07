import Langlands.GroupScheme.Reductive.LocalSplitRootTransport
import Langlands.GroupScheme.Reductive.PinnedIsomorphismProof
import Langlands.GroupScheme.Reductive.PinningLattice
import Langlands.GroupScheme.Rational.SteinbergRootMapUniqueness
import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Rational.RootPointLieEquiv
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights
import Langlands.GroupScheme.Rational.RootKernelTorus

/-! # Split field groups with matching simple-root parametrizations are isomorphic -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

theorem splitTorus.exponentCharacter_neg (S : Scheme.{u}) (I : Type u) [Fintype I]
    (m : I → ℤ) : exponentCharacter S I (-m) = -exponentCharacter S I m := by
  simp only [exponentCharacter, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

namespace LocalSplitCell

section Ring

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}

theorem rootPoint_zero (u : Ga R ⟶ G) (Z : Over (Spec (CommRingCat.of R))) :
    rootPoint u Z 0 = 1 := by
  have h : VectorGroup.scalarPoint (CommRingCat.of R) Z 0 = 1 :=
    VectorGroup.points_ext fun j => by
      rw [VectorGroup.coordinates_scalarPoint, map_one]
      rfl
  rw [rootPoint, h, MonObj.one_comp]

theorem IsRootParametrization.rootPoint_mem {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {m : I → ℤ} {u : Ga R ⟶ G} (hu : IsRootParametrization i m u)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint u Z c ∈ (RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I) i
      (splitTorus.exponentCharacter _ I m)).carrier Z := by
  rw [← hu.represents.2]
  exact ⟨_, rfl⟩

theorem IsRootParametrization.rootPoint_injective
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {m : I → ℤ} {u : Ga R ⟶ G}
    (hu : IsRootParametrization i m u) (Z : Over (Spec (CommRingCat.of R))) :
    Function.Injective (rootPoint u Z) := by
  intro c d h
  have : Mono u.hom.hom := hu.represents.1
  rw [rootPoint, rootPoint] at h
  have h' := congrArg (fun x => (VectorGroup.coordinates (CommRingCat.of R) 1 Z x).toAdd 0)
    ((cancel_mono u.hom.hom).mp h)
  simpa only [VectorGroup.coordinates_scalarPoint] using h'

end Ring

section Field

variable {k : Type u} [Field k] {I : Type u} [Fintype I] {J : Type u}

open CoordinateRootDatum

local instance : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of k) 1

local notation "pt" => 𝟙_ (Over (Spec (CommRingCat.of k)))

theorem one_ne_zero_unit_sections :
    (1 : Γ((𝟙_ (Over (Spec (CommRingCat.of k)))).left, ⊤)) ≠ 0 := by
  intro h
  change (1 : Γ(Spec (CommRingCat.of k), ⊤)) = 0 at h
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom h
  rw [map_one, map_zero] at h'
  exact one_ne_zero h'

theorem fieldRealization_root_eq (P : RootDatum J (I → ℤ) (I → ℤ)) (α : J) :
    (fieldRealization k P).root α = (splitTorus.characterLatticeEquiv k I).symm (P.root α) := by
  rw [fieldRealization_root, splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]

theorem fieldRealization_isReduced {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : P.IsReduced) :
    (fieldRealization k P).IsReduced := by
  refine ⟨fun α β hdep => ?_⟩
  have hdep' : ¬ LinearIndependent ℤ ![P.root α, P.root β] := by
    intro hli
    apply hdep
    convert hli.map_injOn
      (splitTorus.characterLatticeEquiv k I).symm.toIntLinearEquiv.toLinearMap
      (splitTorus.characterLatticeEquiv k I).symm.injective.injOn using 1
    ext a
    fin_cases a <;> simp [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
  rcases (hP.eq_or_eq_neg α β hdep') with h | h
  · left
    rw [fieldRealization_root_eq, fieldRealization_root_eq, h]
  · right
    rw [fieldRealization_root_eq, fieldRealization_root_eq, h, map_neg]

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Reducedness of the coordinate datum excludes every higher multiple of a root. -/
theorem hasNoHigherRoots_fieldRealization {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hred : P.IsReduced)
    (hP : IsRootDatumOf i (fieldRealization k P)) (a : J) :
    RelativeRoot.HasNoHigherRoots i ((fieldRealization k P).root a) := by
  let : (fieldRealization k P).IsReduced := fieldRealization_isReduced hred
  let : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) :=
    IsAddTorsionFree.of_module_rat _
  let : IsAddTorsionFree (characterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) :=
    (isSplitTorus_splitTorus I).character_toRat_injective.isAddTorsionFree toRat
  intro n hn
  let : n.AtLeastTwo := ⟨hn⟩
  rw [relativeRoots_eq_roots, ← hP.2.1]
  exact (fieldRealization k P).nsmul_notMem_range_root

variable (k) in
/-- The Lie algebra of `𝔾ₐ` over a field, identified with the field by the epsilon
coordinate; `1` goes to the standard tangent vector. -/
def gaLieEquiv : k ≃ₗ[k] Additive (lieKernel (Ga k) (CommRingCat.of k)) :=
  (LinearEquiv.funUnique (Fin 1) k k).symm.trans
    (RelativeRoot.vectorLieCoordinates (VectorGroup.coordinates (CommRingCat.of k) 1)
      VectorGroup.isNaturalVectorCoordinates (CommAlgCat.of k k)).symm

theorem gaLieEquiv_one : gaLieEquiv k 1 = VectorGroup.standardEpsilon k := by
  let E := RelativeRoot.vectorLieCoordinates (VectorGroup.coordinates (CommRingCat.of k) 1)
    VectorGroup.isNaturalVectorCoordinates (CommAlgCat.of k k)
  apply E.injective
  change E (E.symm ((LinearEquiv.funUnique (Fin 1) k k).symm 1)) = E (E.symm fun _ => 1)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  funext j
  simp

/-- The field pinning determined by a split maximal torus, a reduced coordinate root
datum with a base, and root parametrizations of the simple roots: the simple-root vector
of `a` is the derivative of `u a` at the standard tangent vector. -/
def fieldPinning (hG : IsConnectedReductive G) (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (hi : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) i) [Finite J]
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hred : P.IsReduced)
    (hP : IsRootDatumOf i (fieldRealization k P)) (b : (fieldRealization k P).Base)
    (u : J → (Ga k ⟶ G)) (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a)) :
    SplitPinning G where
  isConnectedReductive := hG
  torus := splitTorus.commGroupScheme _ I
  inclusion := i
  isSplitTorus := isSplitTorus_splitTorus I
  isMaximalTorus := hi
  rootIndex := J
  rootDatum := fieldRealization k P
  isRootDatum := hP
  isReduced := fieldRealization_isReduced hred
  base := b
  pinning := ⟨fun a =>
    letI := hG.smooth
    (gaLieEquiv k).trans (RelativeRoot.representedRootLieEquiv
      (S := splitTorus.commGroupScheme _ I) (isSplitTorus_splitTorus I) i
      ((fieldRealization k P).ne_zero a) (hasNoHigherRoots_fieldRealization hred hP a)
      (by rw [fieldRealization_root]; exact (hu a a.2).represents))⟩

theorem fieldPinning_rootVector (hG : IsConnectedReductive G)
    (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (hi : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) i) [Finite J]
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hred : P.IsReduced)
    (hP : IsRootDatumOf i (fieldRealization k P)) (b : (fieldRealization k P).Base)
    (u : J → (Ga k ⟶ G)) (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (a : b.support) :
    (fieldPinning hG i hi hred hP b u hu).pinning.rootVector a =
      Lie.targetMapLinear (u a) (CommRingCat.of k) (VectorGroup.standardEpsilon k) := by
  change Lie.targetMapLinear (u a) k (gaLieEquiv k 1) = _
  rw [gaLieEquiv_one]

/-- A root parametrization of a simple root whose derivative is the pinned vector is a
normalized root parametrization of the field pinning. -/
def normalizedOfRootParametrization (hG : IsConnectedReductive G)
    (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (hi : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) i) [Finite J]
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hred : P.IsReduced)
    (hP : IsRootDatumOf i (fieldRealization k P)) (b : (fieldRealization k P).Base)
    (u : J → (Ga k ⟶ G)) (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    {a : J} (ha : a ∈ b.support) (w : Ga k ⟶ G) (hw : IsRootParametrization i (P.root a) w)
    (hd : Lie.targetMapLinear w (CommRingCat.of k) (VectorGroup.standardEpsilon k) =
      Lie.targetMapLinear (u a) (CommRingCat.of k) (VectorGroup.standardEpsilon k)) :
    (fieldPinning hG i hi hred hP b u hu).NormalizedRootParametrization ⟨a, ha⟩ where
  hom := w
  represents := by
    have h := hw.represents
    rw [← fieldRealization_root k P a] at h
    exact h
  isClosedSubgroup := hw.isClosedSubgroup
  torus_equivariant T t c := by
    have h := hw.equivariant T t c
    rw [← fieldRealization_root k P a] at h
    exact h
  derivative := hd.trans (fieldPinning_rootVector hG i hi hred hP b u hu ⟨a, ha⟩).symm

variable {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

/-- **Comparison over a field.** Two connected reductive groups over a field with split
maximal tori `i`, `i'` realizing the same reduced coordinate root datum, with root
parametrizations `u a`, `v a` (resp. `u' a`, `v' a`) of every simple root `a` and its
negative such that `v a (-1) u a (1) v a (-1)` normalizes the torus, are isomorphic by an
isomorphism carrying `i` to `i'`, `u a` to `u' a` and `v a (-1)` to `v' a (-1)`. -/
theorem exists_iso_of_simpleRootParametrizations
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of k)) I ⟶ H}
    (hi : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hi' : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) i') [Finite J]
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hred : P.IsReduced)
    (hP : IsRootDatumOf i (fieldRealization k P)) (hP' : IsRootDatumOf i' (fieldRealization k P))
    (b : (fieldRealization k P).Base) {u v : J → (Ga k ⟶ G)} {u' v' : J → (Ga k ⟶ H)}
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (hv : ∀ a ∈ b.support, IsRootParametrization i (-P.root a) (v a))
    (hn : ∀ a ∈ b.support,
      weylPoint (u a) (v a) ∈ normalizerPoints (T := splitTorus.commGroupScheme _ I) i)
    (hu' : ∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a))
    (hv' : ∀ a ∈ b.support, IsRootParametrization i' (-P.root a) (v' a))
    (hn' : ∀ a ∈ b.support,
      weylPoint (u' a) (v' a) ∈ normalizerPoints (T := splitTorus.commGroupScheme _ I) i') :
    ∃ Φ : G ≅ H, i ≫ Φ.hom = i' ∧ ∀ a ∈ b.support,
      u a ≫ Φ.hom = u' a ∧
        rootPoint (v a) pt (-1) ≫ Φ.hom.hom.hom = rootPoint (v' a) pt (-1) := by
  let p := fieldPinning hG i hi hred hP b u hu
  let q := fieldPinning hH i' hi' hred hP' b u' hu'
  let e : RootPairing.Equiv p.rootDatum q.rootDatum := RootPairing.Equiv.id _
  obtain ⟨f, ⟨hfw, -, hfi⟩, -⟩ := pinnedIsomorphism k G H p q e (fun _ => Iff.rfl)
  have htor : f.torusIso = Iso.refl _ := by
    apply (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I).iso_ext_of_character_congr
    ext χ
    have h1 := LinearEquiv.congr_fun hfw χ
    have h2 : e.weightEquiv χ = χ := rfl
    rw [h2] at h1
    exact h1.trans (Category.id_comp χ).symm
  let Φ := f.groupIso
  have hsq : i ≫ Φ.hom = i' := by
    have h := f.square
    rw [htor] at h
    exact h
  have hsimple : ∀ a (ha : a ∈ b.support), u a ≫ Φ.hom = u' a := by
    intro a ha
    have hq : ∀ x : q.base.support, x.val = a →
        q.pinning.rootVector x = q.pinning.rootVector ⟨a, ha⟩ := by
      rintro ⟨c, hc⟩ rfl
      rfl
    have hd : Lie.targetMapLinear (u a ≫ Φ.hom) (CommRingCat.of k)
          (VectorGroup.standardEpsilon k) =
        Lie.targetMapLinear (u' a) (CommRingCat.of k) (VectorGroup.standardEpsilon k) := by
      rw [Lie.targetMapLinear_comp, LinearMap.comp_apply,
        ← fieldPinning_rootVector hG i hi hred hP b u hu ⟨a, ha⟩]
      have h := (f.rootVector_eq ⟨a, ha⟩).trans (hq _ (by
        change f.indexEquiv a = a
        rw [hfi]
        rfl))
      exact h.trans (fieldPinning_rootVector hH i' hi' hred hP' b u' hu' ⟨a, ha⟩)
    exact SplitPinning.NormalizedRootParametrization.hom_eq
      (normalizedOfRootParametrization hH i' hi' hred hP' b u' hu' ha (u a ≫ Φ.hom)
        ((hu a ha).comp_iso Φ hsq) hd)
      (normalizedOfRootParametrization hH i' hi' hred hP' b u' hu' ha (u' a) (hu' a ha) rfl)
  refine ⟨Φ, hsq, fun a ha => ⟨hsimple a ha, ?_⟩⟩
  have : Mono i'.hom.hom.left := hi'.2.1.mono
  have hχ : splitTorus.exponentCharacter _ I (P.root a) = (fieldRealization k P).root a :=
    (fieldRealization_root k P a).symm
  have hχn : splitTorus.exponentCharacter _ I (-P.root a) = -(fieldRealization k P).root a := by
    rw [splitTorus.exponentCharacter_neg, hχ]
  have hx : rootPoint (u' a) pt 1 ∈
      (RelativeRoot.subgroup i' ((fieldRealization k P).root a)).carrier (Over.mk (𝟙 _)) := by
    rw [← hχ]
    exact (hu' a ha).rootPoint_mem _ 1
  have hx1 : rootPoint (u' a) pt 1 ≠ 1 := by
    rw [← rootPoint_zero (u' a)]
    intro h
    exact one_ne_zero_unit_sections ((hu' a ha).rootPoint_injective _ h)
  have hvΦ := (hv a ha).comp_iso Φ hsq
  have hp : RelativeRoot.IsOppositeFactorPair i' ((fieldRealization k P).root a)
      (rootPoint (u' a) pt 1) (rootPoint (v' a) pt (-1), rootPoint (v' a) pt (-1)) := by
    refine ⟨?_, ?_, hn' a ha⟩
    · rw [← hχn]
      exact (hv' a ha).rootPoint_mem _ _
    · rw [← hχn]
      exact (hv' a ha).rootPoint_mem _ _
  have hq : RelativeRoot.IsOppositeFactorPair i' ((fieldRealization k P).root a)
      (rootPoint (u' a) pt 1) (rootPoint (v a) pt (-1) ≫ Φ.hom.hom.hom,
        rootPoint (v a) pt (-1) ≫ Φ.hom.hom.hom) := by
    have hm := hvΦ.rootPoint_mem pt (-1)
    rw [rootPoint_comp, hχn] at hm
    refine ⟨hm, hm, ?_⟩
    · have hx' : rootPoint (u' a) pt 1 = rootPoint (u a) pt 1 ≫ Φ.hom.hom.hom := by
        rw [← rootPoint_comp, hsimple a ha]
      change (rootPoint (v a) pt (-1) ≫ Φ.hom.hom.hom) * rootPoint (u' a) pt 1 *
        (rootPoint (v a) pt (-1) ≫ Φ.hom.hom.hom) ∈ _
      rw [hx', ← MonObj.mul_comp, ← MonObj.mul_comp]
      exact (normalizerPointsMap (T := splitTorus.commGroupScheme _ I) i Φ.hom i' hsq
        ⟨weylPoint (u a) (v a), hn a ha⟩).property
  have h := RelativeRoot.IsOppositeFactorPair.eq (T := splitTorus.commGroupScheme _ I) i'
    (isSplitTorus_splitTorus I) ((fieldRealization k P).ne_zero a) hx hx1 hp hq
  exact (Prod.ext_iff.mp h).1.symm

end Field

end LocalSplitCell

end Langlands.GroupScheme
