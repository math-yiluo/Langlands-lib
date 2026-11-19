import Langlands.GroupScheme.Torus.CentralRigiditySpreading
import Langlands.GroupScheme.Torus.CentralRigidityTransport
import Langlands.GroupScheme.Torus.MultiplicativeTypeTorsionDeterminationProof
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeTorsion
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.AbelianScheme.Torsion
import Langlands.AlgebraicGeometry.AdicDetectionProof
import Langlands.AlgebraicGeometry.SpecStalkFactorizationSpreadingProof
import Langlands.GroupScheme.Torus.CentralInfinitesimalRigidityReduction
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Central rigidity over a locally noetherian base (SGA 3, IX, Théorème 5.1 a)) -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralRigidityLocal

open RelativeMultiplicativeType CentralRigiditySpreading

/-- For `n > 0`, the `n`-torsion subgroup of a group of multiplicative type is finite over the
base, and every point of order dividing `n` factors through it. -/
theorem exists_finite_torsion {S : Scheme.{u}} {H : GroupScheme S}
    (hH : IsMultiplicativeType H) (n : ℕ) (hn : 0 < n) :
    ∃ (K : GroupScheme S) (i : K ⟶ H), IsFinite K.X.hom ∧
      ∀ (T : Over S) (x : T ⟶ H.X), x ^ n = 1 → ∃ y : T ⟶ K.X, y ≫ i.hom.hom = x := by
  let := hH.isCommMonObj
  have := hH.isSeparated
  obtain ⟨hfin, -, -⟩ := hH.torsion_geometry n hn
  refine ⟨torsion H (n : ℤ), torsionι H (n : ℤ), hfin, ?_⟩
  intro T x hx
  have hx' : x ^ (n : ℤ) = 1 := by rw [zpow_natCast]; exact hx
  obtain ⟨y, hy, -⟩ := (existsUnique_torsion_lift_iff H (n : ℤ) T x).2 hx'
  exact ⟨y, hy⟩

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- If two homomorphisms from a finite group agree modulo every power of the maximal ideal,
they agree. -/
theorem comp_eq_of_adic {K H G : GroupScheme (Spec (CommRingCat.of A))}
    (hK : IsFinite K.X.hom) (i : K ⟶ H) (u v : H ⟶ G)
    (hk : ∀ k : ℕ,
      (GroupScheme.baseChange
          (Spec.algebraMap A (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)))).map u =
        (GroupScheme.baseChange
          (Spec.algebraMap A (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)))).map v) :
    i.hom.hom ≫ u.hom.hom = i.hom.hom ≫ v.hom.hom := by
  have hiso : IsIso (eqIncl (i ≫ u) (i ≫ v)) := by
    refine Langlands.AlgebraicGeometry.AdicDetection.adicImmersionIsIso A K.X.left _ K.X.hom
      (eqIncl (i ≫ u) (i ≫ v)) hK inferInstance fun n => ?_
    let q := Langlands.AlgebraicGeometry.AdicDetection.adicBase A n
    have hq' : q = Spec.algebraMap A (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) := rfl
    let e := eqIncl (i ≫ u) (i ≫ v)
    let m := Langlands.AlgebraicGeometry.AdicDetection.baseChange K.X.hom e q
    have heq : pullback.fst K.X.hom q ≫ (i ≫ u).hom.hom.left =
        pullback.fst K.X.hom q ≫ (i ≫ v).hom.hom.left := by
      apply (baseChange_map_eq_iff q (i ≫ u) (i ≫ v)).1
      rw [Functor.map_comp, Functor.map_comp, hq', hk n]
    obtain ⟨y, hy⟩ := (exists_factor_iff (i ≫ u) (i ≫ v) _).2 heq
    have hfst : m ≫ pullback.fst K.X.hom q = pullback.fst (e ≫ K.X.hom) q ≫ e :=
      pullback.lift_fst _ _ _
    have hsnd : m ≫ pullback.snd K.X.hom q = pullback.snd (e ≫ K.X.hom) q :=
      pullback.lift_snd _ _ _
    have : Mono m := ⟨fun {Z} a b hab => by
      apply pullback.hom_ext
      · apply (cancel_mono e).1
        have h := congrArg (· ≫ pullback.fst K.X.hom q) hab
        simp only [Category.assoc] at h
        rw [hfst] at h
        exact h
      · have h := congrArg (· ≫ pullback.snd K.X.hom q) hab
        simp only [Category.assoc] at h
        rwa [hsnd] at h⟩
    obtain ⟨σ, hσ1, hσ2⟩ : ∃ σ : pullback K.X.hom q ⟶ pullback (e ≫ K.X.hom) q,
        σ ≫ pullback.fst (e ≫ K.X.hom) q = y ∧
          σ ≫ pullback.snd (e ≫ K.X.hom) q = pullback.snd K.X.hom q :=
      ⟨pullback.lift y (pullback.snd K.X.hom q) (by
        rw [← Category.assoc, hy, pullback.condition]),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hσ : σ ≫ m = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        show σ ≫ m ≫ pullback.fst K.X.hom q = 𝟙 _ ≫ pullback.fst K.X.hom q
        rw [hfst, ← Category.assoc, hσ1, hy, Category.id_comp]
      · rw [Category.assoc]
        show σ ≫ m ≫ pullback.snd K.X.hom q = 𝟙 _ ≫ pullback.snd K.X.hom q
        rw [hsnd, hσ2, Category.id_comp]
    have : IsSplitEpi m := IsSplitEpi.mk' ⟨σ, hσ⟩
    exact isIso_of_mono_of_isSplitEpi m
  have h1 := (exists_factor_iff (i ≫ u) (i ≫ v) (𝟙 _)).1 ⟨inv (eqIncl (i ≫ u) (i ≫ v)), by simp⟩
  apply Over.OverMorphism.ext
  simpa using h1

/-- Over a noetherian local base, two homomorphisms from a group of multiplicative type that
agree modulo every power of the maximal ideal agree. -/
theorem eq_of_adic {H G : GroupScheme (Spec (CommRingCat.of A))} (hH : IsMultiplicativeType H)
    (u v : H ⟶ G)
    (hk : ∀ k : ℕ,
      (GroupScheme.baseChange
          (Spec.algebraMap A (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)))).map u =
        (GroupScheme.baseChange
          (Spec.algebraMap A (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)))).map v) :
    u = v := by
  apply (multiplicativeTypeTorsionDetermination _).1 H G hH u v
  intro n hn T x hx
  obtain ⟨K, i, hfin, hfac⟩ := exists_finite_torsion hH n hn
  obtain ⟨y, rfl⟩ := hfac T x hx
  rw [Category.assoc, Category.assoc, comp_eq_of_adic hfin i u v hk]

omit [IsNoetherianRing A] in
/-- Agreement and centrality on the closed fibre give agreement modulo every power of the
maximal ideal. -/
theorem eq_mod_pow_of_residue
    {H G : GroupScheme (Spec (CommRingCat.of A))} (hH : IsMultiplicativeType H) (u v : H ⟶ G)
    (hs : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).map u =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).map v)
    (hc : IsCentral
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).map u))
    (k : ℕ) :
    (GroupScheme.baseChange
        (Spec.algebraMap A (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)))).map u =
      (GroupScheme.baseChange
        (Spec.algebraMap A (A ⧸ IsLocalRing.maximalIdeal A ^ (k + 1)))).map v := by
  let m := IsLocalRing.maximalIdeal A
  let J : Ideal (A ⧸ m ^ (k + 1)) := m.map (Ideal.Quotient.mk (m ^ (k + 1)))
  have hJ : IsNilpotent J := by
    refine ⟨k + 1, ?_⟩
    show (m.map (Ideal.Quotient.mk (m ^ (k + 1)))) ^ (k + 1) = 0
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
    rfl
  let φ : IsLocalRing.ResidueField A →+* (A ⧸ m ^ (k + 1)) ⧸ J :=
    Ideal.Quotient.lift m ((Ideal.Quotient.mk J).comp (Ideal.Quotient.mk (m ^ (k + 1))))
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ ha)
  have hfac : Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) =
      Spec.algebraMap (A ⧸ m ^ (k + 1)) ((A ⧸ m ^ (k + 1)) ⧸ J) ≫
        Spec.algebraMap A (A ⧸ m ^ (k + 1)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  obtain ⟨heq, hcen⟩ :=
    CentralRigidityTransport.baseChange_eq_and_central_of_factor _ _ _ hfac u v hs hc
  exact CentralInfinitesimalRigidity.centralInfinitesimalUniqueness (A ⧸ m ^ (k + 1)) J hJ _ _ _ _
    (hH.baseChange _)
    ((CentralRigidityTransport.baseChange_comp_map_eq_iff _ _ u v).1 heq)
    ((MultiplicativeTypeAffineInfinitesimalCentrality.isCentral_baseChange_comp_iff _ _ u).1 hcen)

/-- **Théorème 5.1 over a noetherian local base**. -/
theorem eq_of_residue
    {H G : GroupScheme (Spec (CommRingCat.of A))} (hH : IsMultiplicativeType H) (u v : H ⟶ G)
    (hs : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).map u =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).map v)
    (hc : IsCentral
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).map u)) :
    u = v :=
  eq_of_adic hH u v (eq_mod_pow_of_residue hH u v hs hc)

/-- **Théorème 5.1 a)** (locally noetherian base). -/
theorem exists_open_eq_of_locallyNoetherian
    (S : Scheme.{u}) [IsLocallyNoetherian S] (H G : GroupScheme S) (hH : IsMultiplicativeType H)
    (u v : H ⟶ G) (s : S)
    (hs : (GroupScheme.baseChange (S.fromSpecResidueField s)).map u =
      (GroupScheme.baseChange (S.fromSpecResidueField s)).map v)
    (hc : IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map u)) :
    ∃ U : S.Opens, s ∈ U ∧
      (GroupScheme.baseChange U.ι).map u = (GroupScheme.baseChange U.ι).map v := by
  have := hH.quasiCompact
  have := hH.isSeparated
  have := hH.locallyOfFinitePresentation
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  refine exists_open_baseChange_eq Langlands.AlgebraicGeometry.specStalkFactorizationSpreading
    u v s inferInstance inferInstance (locallyOfFinitePresentation_eqIncl u v) ?_
  have hs' := (CentralRigidityTransport.baseChange_comp_map_eq_iff (S.fromSpecStalk s)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (S.presheaf.stalk s))))
    u v).1 hs
  have hc' := (MultiplicativeTypeAffineInfinitesimalCentrality.isCentral_baseChange_comp_iff
    (S.fromSpecStalk s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (S.presheaf.stalk s))))
    u).1 hc
  exact eq_of_residue (A := S.presheaf.stalk s) (hH.baseChange _) _ _ hs' hc'

end Langlands.GroupScheme.CentralRigidityLocal
