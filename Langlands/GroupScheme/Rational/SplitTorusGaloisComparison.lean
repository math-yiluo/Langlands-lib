import Langlands.GroupScheme.Reductive.RootDatumWeylNormalizers
import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport

/-! # Comparing a split torus over an intermediate field with a Galois pinning torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable (F K E : Type u) [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
  [Algebra K E] [IsScalarTower F K E]
  (M : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F K)).obj M).X.hom]

/-- Comparison data between a split torus `s : S ⟶ M_K` over an intermediate field `K` and the
torus `T` of Galois pinning data `p` over `E`. It consists of an actual root datum of `s`, a
bijection of root indices and a lattice isomorphism `θ : X_*(S) ≃ X_*(T_E)` matching roots and
coroots, triviality of the star correction for automorphisms fixing `K`, and, for compatible
`σ ∈ Aut_F(K)` and `τ ∈ Aut_F(E)`, a formula for the Galois transport of every dynamic parabolic
of a cocharacter of `S`: when the inverse ordinary Galois action of `τ` carries `θ ν` into the
Weyl orbit of `θ ν'`, the transport of the dynamic parabolic of `ν` is a rational conjugate of the
dynamic parabolic of `ν'`. -/
def SplitTorusGaloisComparison (p : GaloisPinningData F E M)
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    (s : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F K)).obj M) : Prop :=
  ∃ (J : Type u) (P : RootDatum J (characterLattice S) (cocharacterLattice S))
    (_ : IsRootDatumOf s P) (e : J ≃ p.rootIndex)
    (θ : cocharacterLattice S ≃+ cocharacterLattice p.toSplitPinning.torus),
    (∀ j ν, P.root' j ν = p.toSplitPinning.rootDatum.root' (e j) (θ ν)) ∧
    (∀ j, θ (P.coroot j) = p.toSplitPinning.rootDatum.coroot (e j)) ∧
    (∀ τ : E ≃ₐ[F] E, (∀ x : K, τ (algebraMap K E x) = algebraMap K E x) →
      p.galoisAction τ ∈ p.toSplitPinning.rootDatum.weylGroup) ∧
    ∀ (σ : K ≃ₐ[F] K) (τ : E ≃ₐ[F] E),
      (∀ x : K, τ (algebraMap K E x) = algebraMap K E (σ x)) →
      ∀ (ν ν' : cocharacterLattice S) (w : p.toSplitPinning.rootDatum.Aut),
        w ∈ p.toSplitPinning.rootDatum.weylGroup →
        ((p.galoisAction τ)⁻¹).coweightEquiv (θ ν) = w.coweightEquiv (θ ν') →
        ∃ m : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M),
          SubgroupFunctor.galoisTransport F K M σ
              (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ s)) =
            Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ s ≫
              (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso m).hom)

end Langlands.GroupScheme

namespace Langlands.LinearAlgebra

variable {I J X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X']
  [AddCommGroup Y'] (P : RootDatum J X Y) (Q : RootDatum I X' Y') (e : J ≃ I) (θ : Y ≃+ Y')

/-- A lattice isomorphism matching roots and coroots conjugates the Weyl groups. -/
theorem exists_weyl_coweightEquiv_of_root_coroot
    (hroot : ∀ j ν, P.root' j ν = Q.root' (e j) (θ ν))
    (hcoroot : ∀ j, θ (P.coroot j) = Q.coroot (e j))
    (w : Q.Aut) (hw : w ∈ Q.weylGroup) :
    ∃ w' : P.Aut, w' ∈ P.weylGroup ∧ ∀ ν, θ (w'.coweightEquiv ν) = w.coweightEquiv (θ ν) := by
  induction hw using RootPairing.weylGroup.induction with
  | mem i =>
    refine ⟨RootPairing.Equiv.reflection P (e.symm i), P.reflection_mem_weylGroup _, fun ν => ?_⟩
    rw [RootPairing.Equiv.reflection_coweightEquiv, RootPairing.Equiv.reflection_coweightEquiv,
      RootPairing.coreflection_apply, RootPairing.coreflection_apply, map_sub, map_zsmul,
      hcoroot, Equiv.apply_symm_apply]
    congr 2
    have h := hroot (e.symm i) ν
    rw [Equiv.apply_symm_apply] at h
    exact h
  | one => exact ⟨1, one_mem _, fun ν => rfl⟩
  | mul a b _ _ ia ib =>
    obtain ⟨wa, hwa, ha⟩ := ia
    obtain ⟨wb, hwb, hb⟩ := ib
    refine ⟨wa * wb, mul_mem hwa hwb, fun ν => ?_⟩
    simp only [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.coweightEquiv_comp_toLin,
      LinearEquiv.trans_apply]
    rw [hb, ha]

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

variable {F K E : Type u} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
  [Algebra K E] [IsScalarTower F K E]
  {M : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F K)).obj M).X.hom]

/-- Conjugating a dynamic parabolic of a conjugated cocharacter. -/
theorem parabolic_comp_innerIso_comp_innerIso {S : Scheme.{u}} {G : GroupScheme S}
    (χ χ' : (Gm S).toGrp ⟶ G) (n c : Over.mk (𝟙 S) ⟶ G.X)
    (h : Dynamic.parabolic χ = Dynamic.parabolic (χ' ≫ (G.innerIso n).hom)) :
    Dynamic.parabolic (χ ≫ (G.innerIso c).hom) =
      Dynamic.parabolic (χ' ≫ (G.innerIso (c * n)).hom) := by
  have h1 := Dynamic.parabolic_eq_comap_of_iso (χ ≫ (G.innerIso c).hom) (G.innerIso c).symm
  have h2 := Dynamic.parabolic_eq_comap_of_iso ((χ' ≫ (G.innerIso n).hom) ≫ (G.innerIso c).hom)
    (G.innerIso c).symm
  simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h1 h2
  rw [h1, h, ← h2, innerIso_mul_hom]

omit [Algebra K E] [IsScalarTower F K E] in
/-- If the inverse Galois action carries `θ ν` into the Weyl orbit of
`θ ν'`, then the Galois transport of the dynamic parabolic of `ν` is a rational conjugate of the
dynamic parabolic of `ν'`. -/
theorem exists_transport_eq_of_comparison {p : GaloisPinningData F E M}
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {s : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F K)).obj M}
    {J : Type u} {P : RootDatum J (characterLattice S) (cocharacterLattice S)}
    (hP : IsRootDatumOf s P) (e : J ≃ p.rootIndex)
    (θ : cocharacterLattice S ≃+ cocharacterLattice p.toSplitPinning.torus)
    (hroot : ∀ j ν, P.root' j ν = p.toSplitPinning.rootDatum.root' (e j) (θ ν))
    (hcoroot : ∀ j, θ (P.coroot j) = p.toSplitPinning.rootDatum.coroot (e j))
    (σ : K ≃ₐ[F] K) (τ : E ≃ₐ[F] E)
    (c : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M))
    (w₀ : p.toSplitPinning.rootDatum.Aut) (hw₀ : w₀ ∈ p.toSplitPinning.rootDatum.weylGroup)
    (htrans : ∀ ν : cocharacterLattice S,
      SubgroupFunctor.galoisTransport F K M σ
          (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ s)) =
        Dynamic.parabolic (CommGroupScheme.groupHom
            (θ.symm (((p.galoisAction τ)⁻¹ * w₀).coweightEquiv (θ ν))) ≫ s ≫
          (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso c).hom))
    (ν ν' : cocharacterLattice S) (w : p.toSplitPinning.rootDatum.Aut)
    (hw : w ∈ p.toSplitPinning.rootDatum.weylGroup)
    (hνν' : ((p.galoisAction τ)⁻¹).coweightEquiv (θ ν) = w.coweightEquiv (θ ν')) :
    ∃ m : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M),
      SubgroupFunctor.galoisTransport F K M σ
          (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ s)) =
        Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ s ≫
          (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso m).hom) := by
  obtain ⟨w', hw', hθw'⟩ := Langlands.LinearAlgebra.exists_weyl_coweightEquiv_of_root_coroot P
    p.toSplitPinning.rootDatum e θ hroot hcoroot (w * w₀) (mul_mem hw hw₀)
  obtain ⟨n, hn⟩ := hP.exists_parabolic_coweightEquiv s w' hw'
  have hθ : θ.symm (((p.galoisAction τ)⁻¹ * w₀).coweightEquiv (θ ν)) = w'.coweightEquiv ν' := by
    refine (AddEquiv.symm_apply_eq θ).mpr ?_
    rw [hθw']
    change w₀.coweightEquiv (((p.galoisAction τ)⁻¹).coweightEquiv (θ ν)) =
      w₀.coweightEquiv (w.coweightEquiv (θ ν'))
    rw [hνν']
  refine ⟨c * n, ?_⟩
  rw [htrans, hθ, ← Category.assoc,
    parabolic_comp_innerIso_comp_innerIso _ (CommGroupScheme.groupHom ν' ≫ s) n c (hn ν'),
    Category.assoc]

omit [IsScalarTower F K E] in
/-- A root-datum comparison and an explicit transport formula give the Weyl-orbit form of
parabolic transport. The coweight map of a root-pairing equivalence is contravariant. -/
theorem SplitPinning.splitTorusGaloisComparison_of_transport
    (q : SplitPinning ((GroupScheme.baseChange (algebraBaseMap F K)).obj M))
    (p : GaloisPinningData F E M)
    (e : RootPairing.Equiv q.rootDatum p.toSplitPinning.rootDatum)
    (hkernel : ∀ τ : E ≃ₐ[F] E, (∀ x : K, τ (algebraMap K E x) = algebraMap K E x) →
      p.galoisAction τ ∈ p.toSplitPinning.rootDatum.weylGroup)
    (htrans : ∀ (σ : K ≃ₐ[F] K) (τ : E ≃ₐ[F] E),
      algebraBaseMap K E ≫ galoisBaseMap F K σ = galoisBaseMap F E τ ≫ algebraBaseMap K E →
      ∃ (c : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F K)).obj M))
        (w : p.toSplitPinning.rootDatum.Aut), w ∈ p.toSplitPinning.rootDatum.weylGroup ∧
        ∀ ν : cocharacterLattice q.torus,
          SubgroupFunctor.galoisTransport F K M σ
            (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ q.inclusion)) =
          Dynamic.parabolic (CommGroupScheme.groupHom (e.coweightEquiv (w.coweightEquiv.symm
            (cocharacterLattice.galoisRepresentation F E p.torus τ (e.coweightEquiv.symm ν)))) ≫
            q.inclusion ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso c).hom)) :
    SplitTorusGaloisComparison F K E M p q.inclusion := by
  let θ := e.coweightEquiv.symm.toAddEquiv
  have hroot (j : q.rootIndex) (ν : cocharacterLattice q.torus) :
      q.rootDatum.root' j ν = p.toSplitPinning.rootDatum.root' (e.indexEquiv j) (θ ν) := by
    have h := DFunLike.congr_fun (e.toHom.weight_coweight_transpose_apply q.rootDatum
      p.toSplitPinning.rootDatum (θ ν)) (q.rootDatum.root j)
    change (p.toSplitPinning.rootDatum.flip.toPerfPair (θ ν))
        (e.toHom.weightMap (q.rootDatum.root j)) =
      (q.rootDatum.flip.toPerfPair (e.toHom.coweightMap (θ ν))) (q.rootDatum.root j) at h
    rw [RootPairing.Hom.root_weightMap_apply] at h
    have hν : e.toHom.coweightMap (θ ν) = ν := e.coweightMap_coweightEquiv_symm ν
    rw [hν] at h
    exact h.symm
  have hcoroot (j : q.rootIndex) :
      θ (q.rootDatum.coroot j) = p.toSplitPinning.rootDatum.coroot (e.indexEquiv j) := by
    apply e.coweightEquiv.injective
    change e.coweightEquiv (e.coweightEquiv.symm (q.rootDatum.coroot j)) =
      e.coweightEquiv (p.toSplitPinning.rootDatum.coroot (e.indexEquiv j))
    rw [LinearEquiv.apply_symm_apply, RootPairing.Equiv.coweightEquiv_apply,
      RootPairing.Hom.coroot_coweightMap_apply, Equiv.symm_apply_apply]
  refine ⟨q.rootIndex, q.rootDatum, q.isRootDatum, e.indexEquiv, θ, hroot, hcoroot, hkernel, ?_⟩
  intro σ τ hστ ν ν' w hw hνν'
  obtain ⟨c, w₀, hw₀, hc⟩ := htrans σ τ
    (StarActionFiniteStage.algebraBaseMap_comp_galoisBaseMap σ τ hστ)
  have haction (x : cocharacterLattice p.toSplitPinning.torus) :
      ((p.galoisAction τ)⁻¹).coweightEquiv x =
        cocharacterLattice.galoisRepresentation F E p.torus τ x := by
    rw [← map_inv, RootPairing.Equiv.coweightEquiv_apply]
    change cocharacterLattice.galoisRepresentation F E p.torus τ⁻¹⁻¹ x = _
    rw [inv_inv]
  refine exists_transport_eq_of_comparison q.isRootDatum e.indexEquiv θ hroot hcoroot
    σ τ c w₀⁻¹ (inv_mem hw₀) (fun x => ?_) ν ν' w hw hνν'
  change _ = Dynamic.parabolic (CommGroupScheme.groupHom
    (e.coweightEquiv ((w₀⁻¹).coweightEquiv (((p.galoisAction τ)⁻¹).coweightEquiv (θ x)))) ≫
      q.inclusion ≫ (((GroupScheme.baseChange (algebraBaseMap F K)).obj M).innerIso c).hom)
  rw [haction, RootPairing.Equiv.coweightEquiv_inv]
  exact hc x

end Langlands.GroupScheme
