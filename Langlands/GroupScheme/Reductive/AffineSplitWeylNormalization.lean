import Langlands.GroupScheme.Reductive.LocalWeylNormalizationProof
import Langlands.GroupScheme.Reductive.LocalRankOneWeylNormalization
import Langlands.GroupScheme.Reductive.LocalSplitRootPairLaws
import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell
import Langlands.GroupScheme.Reductive.LocalSplitLocalAlgebraCellIsomorphism
import Langlands.GroupScheme.Reductive.GlobalSplitRootParametrization
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Weyl normalization of opposite root pairs over an arbitrary commutative ring -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineSplitWeylNormalization

open LocalSplitCell LocalSplitRootBaseChange
open Corepresented.RingCoordinates

/-! ### Weyl points from local-ring points -/

section WeylLocal

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Over a base change to a commutative algebra `A`, the Weyl-point identity of the
base-changed root maps is the Weyl-point identity of the original root maps on the test
schemes coming from `A`. -/
theorem isWeylPoint_apply_of_baseChange {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {u v : Ga R ⟶ G} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)} (A : Type u) [CommRing A] [Algebra R A]
    (h : IsWeylPoint (splitTorus.baseChangeHom (K := A) G I i)
      (weylPoint (baseChangeRoot A u) (baseChangeRoot A v)) f)
    (Z : Over (Spec (CommRingCat.of A)))
    (t : (Over.map (algebraBaseMap R A)).obj Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    (toUnit _ ≫ weylPoint u v) * (t ≫ i.hom.hom) * (toUnit _ ≫ weylPoint u v)⁻¹ =
      t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom := by
  let E := GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
  let ET := GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) Z
  let Z' := (Over.map (algebraBaseMap R A)).obj Z
  obtain ⟨t₀, rfl⟩ : ∃ t₀ : Z ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X,
      ET (t₀ ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) = t := by
    refine ⟨ET.symm t ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).hom.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id,
      MulEquiv.apply_symm_apply]
  have hN : E (toUnit Z ≫ weylPoint (baseChangeRoot A u) (baseChangeRoot A v)) =
      toUnit Z' ≫ weylPoint u v := by
    rw [toUnit_comp_eq_constantPoint, constantPoint_weylPoint, map_mul, map_mul,
      baseChangePointsEquiv_rootPoint, baseChangePointsEquiv_rootPoint,
      toUnit_comp_eq_constantPoint, constantPoint_weylPoint]
  have hexp : (splitTorus.exponentIso (Spec (CommRingCat.of A)) I f).hom ≫
      (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv =
        (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫
          (GroupScheme.baseChange (algebraBaseMap R A)).map
            (splitTorus.exponentIso (Spec (CommRingCat.of R)) I f).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc,
      splitTorus.exponentIso_baseChange (Spec (CommRingCat.of R)) I (algebraBaseMap R A) f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ht : ET ((t₀ ≫ (splitTorus.exponentIso _ I f).hom.hom.hom) ≫
      (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) =
        ET (t₀ ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) ≫
          (splitTorus.exponentIso (Spec (CommRingCat.of R)) I f).hom.hom.hom := by
    rw [← GroupScheme.baseChangePointsEquiv_comp, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hexp]
  have hw := congrArg E (h Z t₀)
  rw [map_mul, map_mul, map_inv, hN, baseChangePointsEquiv_torus, ← Category.assoc,
    baseChangePointsEquiv_torus, ht, Category.assoc] at hw
  exact hw

/-- **Weyl points from local-ring points.** The Weyl point of two root maps normalizes the
torus through `f` as soon as this holds after base change to every commutative local
algebra. -/
theorem isWeylPoint_of_localBaseChange [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {u v : Ga R ⟶ G}
    {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A],
      IsWeylPoint (splitTorus.baseChangeHom (K := A) G I i)
        (weylPoint (baseChangeRoot A u) (baseChangeRoot A v)) f) :
    IsWeylPoint i (weylPoint u v) f := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro Z t
  apply Over.OverMorphism.ext
  apply CellGluing.hom_ext_of_localRingPoints
  intro A _ _ x
  let s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := x ≫ Z.hom
  let : Algebra R A := (Spec.preimage s).hom.toAlgebra
  have hs : algebraBaseMap R A = s := Spec.map_preimage s
  let Z₀ : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  let q : (Over.map (algebraBaseMap R A)).obj Z₀ ⟶ Z := Over.homMk x (by
    change x ≫ Z.hom = 𝟙 _ ≫ algebraBaseMap R A
    rw [Category.id_comp, hs])
  have h1 := isWeylPoint_apply_of_baseChange A (h A) Z₀ (q ≫ t)
  have h2 : q ≫ ((toUnit Z ≫ weylPoint u v) * (t ≫ i.hom.hom) *
      (toUnit Z ≫ weylPoint u v)⁻¹) =
        q ≫ t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom ≫ i.hom.hom := by
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit]
    simpa only [Category.assoc] using h1
  exact congrArg CommaMorphism.left h2

end WeylLocal

/-! ### The dual-number computation over a commutative algebra -/

section RingCoord

variable {R : Type u} [CommRing R] (k : Type u) [CommRing k] [Algebra R k]

/-- The map `R[ε] → k[ε]`, `r + sε ↦ r + sε`. -/
def ringDualMap : DualNumber R →ₐ[R] DualNumber k :=
  DualNumber.lift ⟨(Algebra.ofId R (DualNumber k), DualNumber.eps), DualNumber.eps_mul_eps,
    fun _ => DualNumber.commute_eps_left _⟩

theorem ringDualMap_eps : ringDualMap k (DualNumber.eps : DualNumber R) = DualNumber.eps :=
  DualNumber.lift_apply_eps _

theorem snd_ringDualMap (x : DualNumber R) :
    (ringDualMap k x).snd = algebraMap R k x.snd := by
  rw [ringDualMap, DualNumber.lift_apply_apply]
  simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl']

/-- The unit `1 + cε` of `k[ε]`. -/
def ringDualUnit (c : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr c
  inv := 1 - TrivSqZeroExt.inr c
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, TrivSqZeroExt.inr_mul_inr]
    abel
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, TrivSqZeroExt.inr_mul_inr]
    abel

variable {k} {I : Type u} [Fintype I] {G : GroupScheme (Spec (CommRingCat.of R))}
  (D : Type u) [CommRing D] [Algebra R D] [Algebra k D] [IsScalarTower R k D]

theorem testOverHom_appTop (c : Γ((testOver k D).left, ⊤)) :
    (testOverHom (CommRingCat.of R) k D).left.appTop c = c := by
  change (𝟙 (Spec (CommRingCat.of D)) : _ ⟶ _).appTop c = c
  rw [Scheme.Hom.id_appTop]
  rfl

/-- Values of a base-changed root map over `Spec D`, regarded over `Spec R`. -/
theorem testOverHom_rootPoint (w : Ga R ⟶ G) (c : Γ((testOver k D).left, ⊤)) :
    testOverHom (CommRingCat.of R) k D ≫
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G (testOver k D)
          (rootPoint (baseChangeRoot k w) (testOver k D) c) =
      rootPoint w (specOver (CommRingCat.of R) D) c := by
  rw [baseChangePointsEquiv_rootPoint, comp_rootPoint, testOverHom_appTop]

/-- Torus values of the base-changed torus over `Spec D`, regarded over `Spec R`. -/
theorem testOverHom_torus [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (t : testOver k D ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) :
    testOverHom (CommRingCat.of R) k D ≫
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G (testOver k D)
          (t ≫ (splitTorus.baseChangeHom (K := k) G I i).hom.hom) =
      (testOverHom (CommRingCat.of R) k D ≫
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) (splitTorus _ I) (testOver k D)
          (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R k) I).inv.hom.hom)) ≫ i.hom.hom := by
  rw [baseChangePointsEquiv_torus, Category.assoc]

theorem baseScalar_testOver (d : k) :
    baseScalar (testOver k D) d = (Scheme.ΓSpecIso (CommRingCat.of D)).inv (algebraMap k D d) := by
  change (Spec.map (CommRingCat.ofHom (algebraMap k D))).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv d) = _
  rw [LocalWeylNormalization.specMap_appTop_inv]
  rfl

theorem ringDualMap_appTop_epsSec :
    (specMapOver (ringDualMap (R := R) k)).left.appTop (LocalWeylNormalization.epsSec R) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv DualNumber.eps := by
  change (Spec.map (CommRingCat.ofHom (ringDualMap (R := R) k).toRingHom)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv DualNumber.eps) = _
  rw [LocalWeylNormalization.specMap_appTop_inv]
  exact congrArg _ (ringDualMap_eps k)

variable {J : Type u}

/-- **The `ε`-coefficient over an algebra satisfying the rank-one laws.** If
`u(1) v(ε) = y ≫ cellMap` over `R[ε]` and, over a commutative `R`-algebra `k`, the root map
`u` and the rescaling `v(d ·)` by a unit `d` satisfy the four rank-one laws, then the
`ε`-coefficient of the `u`-coordinate of `y` maps to `-d⁻¹` in `k`. -/
theorem algebraMap_snd_posCoord_of_rankOneLaws [DecidableEq I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (fam : J → (Ga R ⟶ G)) {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [Mono (cellMap i fam neg pos).left] (kn : Fin m) (kp : Fin n)
    (y : LocalWeylNormalization.dualOver R ⟶ cellObj R I m n)
    (hy : y ≫ cellMap i fam neg pos =
      rootPoint (fam (pos kp)) _ 1 * rootPoint (fam (neg kn)) _ (LocalWeylNormalization.epsSec R))
    (d : kˣ) (nu : I → ℤ)
    (hlaws : RankOneLaws (splitTorus.baseChangeHom (K := k) G I i) nu
      (baseChangeRoot k (fam (pos kp))) (scaleHom (d : k) ≫ baseChangeRoot k (fam (neg kn)))) :
    algebraMap R k ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom
      (posCoord y kp)).snd = -(↑d⁻¹ : k) := by
  let Zk := testOver k (DualNumber k)
  let gam := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv
  let u0 := ringDualUnit k (↑d⁻¹ : k)
  let Uz : Γ(Zk.left, ⊤)ˣ := Units.map gam.hom.toMonoidHom u0
  let ye : Γ(Zk.left, ⊤) := gam (TrivSqZeroExt.inr (↑d⁻¹ : k))
  have hR := hlaws.2.2.2 Zk 1 ye Uz (by
    rw [one_mul]
    change gam (1 + TrivSqZeroExt.inr (↑d⁻¹ : k)) = _
    rw [map_add, map_one])
  have hUinv : ((Uz⁻¹ : Γ(Zk.left, ⊤)ˣ) : Γ(Zk.left, ⊤)) = gam ↑u0⁻¹ := rfl
  rw [rootPoint_scaleHom, rootPoint_scaleHom, mul_one, hUinv] at hR
  have hT := congrArg (fun x => testOverHom (CommRingCat.of R) k (DualNumber k) ≫
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G Zk x) hR
  simp only [map_mul, MonObj.comp_mul] at hT
  rw [testOverHom_rootPoint, testOverHom_rootPoint, testOverHom_rootPoint, testOverHom_rootPoint,
    testOverHom_torus] at hT
  have heps : baseScalar Zk (d : k) * ye = gam DualNumber.eps := by
    rw [baseScalar_testOver]
    refine ((map_mul gam.hom _ _).symm).trans (congrArg gam.hom ?_)
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr, smul_eq_mul,
      Units.mul_inv]
    rfl
  rw [heps] at hT
  let ψ : specOver (CommRingCat.of R) (DualNumber k) ⟶ LocalWeylNormalization.dualOver R :=
    specMapOver (ringDualMap (R := R) k)
  have hcell := (comp_cellMap i fam neg pos (ψ ≫ y)).symm
  rw [Category.assoc, hy, MonObj.comp_mul, comp_rootPoint, comp_rootPoint, map_one,
    ringDualMap_appTop_epsSec, hT, ← LocalWeylNormalization.cellPoint_single] at hcell
  have hp := congrFun (LocalWeylNormalization.posCoord_eq_of_cellPoint_eq i fam neg pos hcell) kp
  rw [posCoord_comp, Pi.single_eq_same] at hp
  have hp2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom hp
  change (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom
    ((Spec.map (CommRingCat.ofHom (ringDualMap (R := R) k).toRingHom)).appTop (posCoord y kp)) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv ↑u0⁻¹) at hp2
  rw [LocalWeylNormalization.ΓSpecIso_hom_specMap_appTop, Iso.inv_hom_id_apply] at hp2
  have hs := congrArg TrivSqZeroExt.snd hp2
  change (ringDualMap k _).snd = _ at hs
  rw [snd_ringDualMap] at hs
  rw [hs]
  change (1 - TrivSqZeroExt.inr (↑d⁻¹ : k) : DualNumber k).snd = -(↑d⁻¹ : k)
  simp

end RingCoord

/-! ### Weyl normalization over an arbitrary commutative ring -/

section Global

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]

/-- **Weyl normalization of an opposite root pair over an arbitrary commutative ring.** Given
root parametrizations `fam` of all roots and a positive root `a`, the parametrization of `-a`
can be rescaled by a unit `d` of `R` so that the Weyl point of `fam a` and the rescaled map
acts on the torus by the reflection in `a`. The scalar is the inverse of minus the
`ε`-coefficient of the `fam a`-coordinate of `u(1) v(ε)` in the big cell over `R[ε]`. -/
theorem exists_unit_weylNormalization_global (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (b : P.Base) (fam : J → (Ga R ⟶ G))
    (hfam : ∀ α, IsRootParametrization i (P.root α) (fam α)) {a : J} (hpos : b.IsPos a) :
    ∃ d : Rˣ, IsWeylPoint i (weylPoint (fam a) (scaleHom (d : R) ≫ fam (P.reflectionPerm a a)))
      (P.reflection a) := by
  classical
  have := hP.finite
  have hneg : ¬ b.IsPos (P.reflectionPerm a a) := by
    intro h
    let _ := P.indexNeg
    change 0 < b.height (-a) at h
    rw [RootPairing.Base.height_reflectionPerm_self] at h
    rw [RootPairing.Base.isPos_iff] at hpos
    omega
  have hroot : P.root (P.reflectionPerm a a) = -P.root a := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  let pos := (Finite.equivFin {α // b.IsPos α}).symm
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b fam hfam neg pos
  let kn := neg.symm ⟨P.reflectionPerm a a, hneg⟩
  let kp := pos.symm ⟨a, hpos⟩
  have hkn : fam (neg kn : J) = fam (P.reflectionPerm a a) := by
    rw [Equiv.apply_symm_apply]
  have hkp : fam (pos kp : J) = fam a := by
    rw [Equiv.apply_symm_apply]
  obtain ⟨y, hy⟩ := LocalWeylNormalization.exists_dualCellLift i fam (fun k => (neg k : J))
    (fun k => (pos k : J)) kn kp
  let c : R := -((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom (posCoord y kp)).snd
  have key : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A], ∃ δ : Aˣ,
      IsWeylPoint (splitTorus.baseChangeHom (K := A) G I i)
        (weylPoint (baseChangeRoot A (fam a))
          (scaleHom (δ : A) ≫ baseChangeRoot A (fam (P.reflectionPerm a a)))) (P.reflection a) ∧
      algebraMap R A c = ↑δ⁻¹ := by
    intro A _ _ _
    let : Smooth G.X.hom := hG.smooth
    let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))
    have hiA : IsClosedSubgroup (splitTorus.baseChangeHom (K := A) G I i) :=
      IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm
        (hi.baseChange (algebraBaseMap R A))
    have hmaxA : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I)
        (splitTorus.baseChangeHom (K := A) G I i) :=
      splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmax
    have hPA := hP.baseChange_implicit (A := A)
    have hGA := hG.baseChange (algebraBaseMap R A)
    have hpA := isRootParametrization_baseChangeRoot A i _ _ (hfam a)
    have hmA : IsRootParametrization (splitTorus.baseChangeHom (K := A) G I i) (-P.root a)
        (baseChangeRoot A (fam (P.reflectionPerm a a))) := by
      rw [← hroot]
      exact isRootParametrization_baseChangeRoot A i _ _ (hfam _)
    obtain ⟨δ, hδ⟩ := LocalSplitCell.exists_unit_weylNormalization hGA _ hiA hmaxA hPA a hpA hmA
    refine ⟨δ, hδ, ?_⟩
    have hlaws := localSplitRootPairLaws A _ hGA I _ hiA hmaxA J P hPA a _ _ hpA (hmA.scale δ) hδ
    have h := algebraMap_snd_posCoord_of_rankOneLaws i fam (fun k => (neg k : J))
      (fun k => (pos k : J)) kn kp y hy δ (P.coroot a) (by rw [hkp, hkn]; exact hlaws)
    rw [map_neg, h, neg_neg]
  have hcu : IsUnit c := by
    by_contra hc
    obtain ⟨M, hM, hcM⟩ := exists_max_ideal_of_mem_nonunits hc
    have := hM.isPrime
    obtain ⟨δ, -, hδ⟩ := key (Localization.AtPrime M)
    have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime M) M c).mp
      (by rw [hδ]; exact Units.isUnit _)
    exact hu hcM
  refine ⟨hcu.unit⁻¹, ?_⟩
  apply isWeylPoint_of_localBaseChange
  intro A _ _ _
  obtain ⟨δ, hδ, hc⟩ := key A
  have hd : algebraMap R A (↑hcu.unit⁻¹ : R) = δ := by
    have h1 : algebraMap R A (↑hcu.unit⁻¹ : R) * ↑δ⁻¹ = 1 := by
      rw [← hc, ← map_mul, IsUnit.val_inv_mul, map_one]
    calc algebraMap R A (↑hcu.unit⁻¹ : R)
        = algebraMap R A (↑hcu.unit⁻¹ : R) * ↑δ⁻¹ * δ := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = δ := by rw [h1, one_mul]
  rw [LocalSplitRootBaseChange.baseChangeRoot_scaleHom, hd]
  exact hδ

/-- **Weyl-normalized simple-root data over an arbitrary commutative ring.** If every root
space is free of rank one, then for every base `b` there are root parametrizations of the
simple roots and their negatives whose Weyl points `u_{-a}(-1) u_a(1) u_{-a}(-1)` act on the
torus by the simple reflections. This is the conclusion of
`LocalSplitSimpleRootGroupLocalStatement` over an arbitrary commutative ring. -/
theorem exists_simpleRootFamily_of_free (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (b : P.Base) :
    ∃ u : J → (Ga R ⟶ G),
      (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
        IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a))) ∧
      ∀ a ∈ b.support,
        IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a) := by
  classical
  choose u hu using fun α =>
    LocalRootGroup.exists_rootParametrization_of_free_weight i hG hmax hP α (hfree α)
  choose d hd using fun a : b.support =>
    exists_unit_weylNormalization_global hG i hi hmax hP b u hu
      (RootPairing.Base.isPos_of_mem_support a.2)
  let v : b.support → (Ga R ⟶ G) := fun a =>
    scaleHom (d a : R) ≫ u (P.reflectionPerm a a)
  have hv (a : b.support) :
      IsRootParametrization i (P.root (P.reflectionPerm a a)) (v a) ∧
        IsWeylPoint i (weylPoint (u a) (v a)) (P.reflection a) :=
    ⟨(hu (P.reflectionPerm a a)).scale (d a), hd a⟩
  have hnm : ∀ a : b.support, P.reflectionPerm a a ∉ b.support := fun a h => by
    have hne : P.reflectionPerm a a ≠ a := fun h' => P.ne_neg (i := (a : J)) h'.symm
    apply b.root_ne_neg_of_ne h a.2 hne
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have hinj : ∀ a a' : b.support, P.reflectionPerm a' a' = P.reflectionPerm a a → a' = a := by
    intro a a' h
    apply Subtype.ext
    apply P.root.injective
    have h' := congrArg P.root h
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
      RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, neg_inj] at h'
    exact h'
  let u' : J → (Ga R ⟶ G) := fun α =>
    if h : ∃ a : b.support, P.reflectionPerm a a = α then v h.choose else u α
  have hs : ∀ a ∈ b.support, u' a = u a := by
    intro a ha
    refine dite_eq_right ?_
    rintro ⟨a', ha'⟩
    exact hnm a' (ha' ▸ ha)
  have hn : ∀ a : b.support, u' (P.reflectionPerm a a) = v a := by
    intro a
    have h : ∃ a' : b.support, P.reflectionPerm a' a' = P.reflectionPerm a a := ⟨a, rfl⟩
    change (if h : ∃ a' : b.support, P.reflectionPerm a' a' = P.reflectionPerm a a
      then v h.choose else u (P.reflectionPerm a a)) = v a
    rw [dite_eq_left h, hinj a _ h.choose_spec]
  refine ⟨u', fun a ha => ⟨?_, ?_⟩, fun a ha => ?_⟩
  · rw [hs a ha]
    exact hu a
  · have hn' : u' (P.reflectionPerm a a) = v ⟨a, ha⟩ := hn ⟨a, ha⟩
    rw [hn']
    exact (hv ⟨a, ha⟩).1
  · have hn' : u' (P.reflectionPerm a a) = v ⟨a, ha⟩ := hn ⟨a, ha⟩
    rw [hs a ha, hn']
    exact (hv ⟨a, ha⟩).2

end Global

end Langlands.GroupScheme.AffineSplitWeylNormalization

/-! ### The statement -/

namespace Langlands.GroupScheme

open LocalSplitCell

/-- **Weyl-normalized simple-root data over an arbitrary commutative ring.** Let `G` be a
reductive group scheme over `Spec R` (`R` any commutative ring) with a closed coordinate split
torus `i`, maximal on every residue-field fibre, and a root datum `P` that is the root datum of
the torus on every field-valued fibre, such that every root space is free of rank one. Then for
every base `b` there are root parametrizations of the simple roots and their negatives whose
Weyl points `u_{-a}(-1) u_a(1) u_{-a}(-1)` act on the torus by the simple reflections. This is
`LocalSplitSimpleRootGroupLocalStatement` with the local-ring hypothesis replaced by freeness
of the root spaces. -/
def AffineSplitSimpleRootGroupStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
      (∀ α : J, Nonempty
        (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
      ∀ b : P.Base, ∃ u : J → (Ga R ⟶ G),
        (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
          IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a))) ∧
        ∀ a ∈ b.support,
          IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a)

/-- Proof of `AffineSplitSimpleRootGroupStatement`, by
`AffineSplitWeylNormalization.exists_simpleRootFamily_of_free`. -/
theorem affineSplitSimpleRootGroup : AffineSplitSimpleRootGroupStatement.{u} := by
  intro R _ G _ hG I _ _ i hi hmax J P hP hfree b
  exact AffineSplitWeylNormalization.exists_simpleRootFamily_of_free hG i hi hmax hP hfree b

end Langlands.GroupScheme
