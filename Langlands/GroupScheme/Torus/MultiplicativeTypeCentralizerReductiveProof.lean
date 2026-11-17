import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralizerReductiveStatement
import Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelProof
import Langlands.GroupScheme.AutomorphicAction.AffineCocycleQuotient
import Langlands.GroupScheme.Torus.CocycleModelActionRelationSmoothProof
import Langlands.GroupScheme.SmoothActionAffineOrbitProof
import Langlands.GroupScheme.Torus.DiagonalizableFixedSmoothProof
import Langlands.GroupScheme.Rational.KernelCentralizerSmooth
import Langlands.GroupScheme.Reductive.AffineHomogeneousQuotientProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Torus.DiagonalizableGeometry

/-! # Centralizers of multiplicative-type groups in connected reductive groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace MultiplicativeTypeCentralizer

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  {H : CommGroupScheme (Spec (CommRingCat.of K))}
  {Λ : Type u} [AddCommGroup Λ]

/-- Conjugation through `i`, with the acting group reparametrized as `D(Λ)` through `e`. -/
def splitAction (e : H.toGrp ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)
    (i : H.toGrp ⟶ G) :
    AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp G :=
  (AutomorphicAction.conjugation i).restrict e.inv

/-- The reparametrized conjugation action has the all-test centralizer of `i` as its
fixed subgroup functor. -/
theorem splitAction_fixedSubgroup
    (e : H.toGrp ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)
    (i : H.toGrp ⟶ G) :
    (splitAction e i).fixedSubgroup = torusCentralizer i := by
  rw [← AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer]
  exact AutomorphicAction.fixedSubgroup_restrict_iso _ e.symm

variable [AddGroup.FG Λ]

/-- Over a field where the acting group is diagonalizable, every representative of the
centralizer in a smooth affine group has an affine homogeneous quotient. -/
theorem exists_affineQuotient_of_split [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (e : H.toGrp ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)
    (i : H.toGrp ⟶ G) {C : GroupScheme (Spec (CommRingCat.of K))} (j : C ⟶ G)
    (hrep : (torusCentralizer i).IsRepresentedBy j) :
    ∃ Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient j,
      IsAffineHom Q.scheme.hom := by
  let a := splitAction e i
  have hrep' : a.fixedSubgroup.IsRepresentedBy j := by
    rw [splitAction_fixedSubgroup]
    exact hrep
  obtain ⟨M, hMaff, hMft⟩ :=
    AutomorphicAction.AffineFiniteTypeCocycleModelProof.affineFiniteTypeCocycleModel K
      (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp G a
  let : IsAffineHom M.scheme.hom := hMaff
  let : LocallyOfFiniteType M.scheme.hom := hMft
  have hrel : Smooth M.actionRelation.left :=
    Diagonalizable.cocycleModelActionRelationSmooth K Λ G a M
  obtain ⟨O, p, f, hOaff, _hOft, _hOqc, hfopen, _hfclosed, hp, hs, _hpqc, hf⟩ :=
    SchemeAction.smoothActionAffineOrbit K G M.scheme M.action hrel M.basepoint
  let : IsAffineHom O.hom := hOaff
  let : IsOpenImmersion f.left := hfopen
  let : Mono f := Over.mono_of_mono_left f
  have hf' : p ≫ f = M.orbit := hf
  exact ⟨M.affineHomogeneousQuotientOfOrbit j hrep' O p f hf' hp hs,
    M.affineHomogeneousQuotientOfOrbit_isAffineHom j hrep' O p f hf' hp hs⟩

/-- Over a field where the acting group is diagonalizable, every closed representative of
the centralizer in a smooth affine group is smooth. -/
theorem smooth_of_split (hGs : Smooth G.X.hom) (hGa : IsAffineHom G.X.hom)
    (e : H.toGrp ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)
    (i : H.toGrp ⟶ G) {C : GroupScheme (Spec (CommRingCat.of K))} (j : C ⟶ G)
    (hrep : (torusCentralizer i).IsRepresentedBy j) (hclosed : IsClosedSubgroup j) :
    Smooth C.X.hom := by
  have hrep' : (AutomorphicAction.conjugation i).fixedSubgroup.IsRepresentedBy j := by
    rw [AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer]
    exact hrep
  exact Diagonalizable.fixedSubgroup_smooth_of_actingIso
    Diagonalizable.FixedSmooth.fixedSubgroupSmooth (AutomorphicAction.conjugation i) e
    hGs hGa j hrep' hclosed

/-- Over a field where the acting group is diagonalizable, the identity component of a
smooth closed representative of the centralizer in a connected reductive group is
connected reductive. -/
theorem isConnectedReductive_of_split (hG : IsConnectedReductive G)
    (e : H.toGrp ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)
    (i : H.toGrp ⟶ G) {C : GroupScheme (Spec (CommRingCat.of K))} (j : C ⟶ G)
    (hrep : (torusCentralizer i).IsRepresentedBy j) (hclosed : IsClosedSubgroup j)
    [Smooth C.X.hom] [IsAffineHom C.X.hom] :
    IsConnectedReductive (identityComponent C) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨Q, hQ⟩ := exists_affineQuotient_of_split e i j hrep
  exact affineHomogeneousQuotientReductive K G hG C j hclosed inferInstance Q hQ

end MultiplicativeTypeCentralizer

open MultiplicativeTypeCentralizer in
/-- **Centralizers of groups of multiplicative type** (Conrad, Remark 3.1.5, field case;
Conrad–Gabber–Prasad, Propositions A.8.10(2) and A.8.12). -/
theorem multiplicativeTypeCentralizerReductive :
    MultiplicativeTypeCentralizerReductiveStatement.{u} := by
  intro k _ G hG H i hH C j hrep hclosed
  obtain ⟨K, _, _, Λ, _, _, ⟨e⟩⟩ := hH
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨hbs, hbf, hbq⟩ := fieldExtension_fpqc k K
  let : Surjective b := hbs
  let : Flat b := hbf
  let : QuasiCompact b := hbq
  have hGK : IsConnectedReductive ((GroupScheme.baseChange b).obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  have hrepK : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj H)
      ((GroupScheme.baseChange b).map i)).IsRepresentedBy
        ((GroupScheme.baseChange b).map j) := by
    rw [torusCentralizer_baseChange]
    exact hrep.baseChange b
  have hclosedK : IsClosedSubgroup ((GroupScheme.baseChange b).map j) :=
    hclosed.baseChange b
  have hCK : Smooth ((GroupScheme.baseChange b).obj C).X.hom :=
    smooth_of_split hGK.smooth hGK.isAffineHom e _ _ hrepK hclosedK
  have hC : Smooth C.X.hom := smooth_of_baseChange b C hCK
  refine ⟨hC, ?_⟩
  let : Smooth C.X.hom := hC
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion j.hom.hom.left := hclosed
  let : IsAffineHom C.X.hom := by
    have h : IsAffineHom (j.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  change IsConnectedReductive (identityComponent C)
  apply IsConnectedReductive.of_fieldExtension (K := K)
  exact IsConnectedReductive.of_iso (IdentityComponent.baseChangeIso C (algebraMap k K))
    (isConnectedReductive_of_split hGK e _ _ hrepK hclosedK)

end Langlands.GroupScheme
