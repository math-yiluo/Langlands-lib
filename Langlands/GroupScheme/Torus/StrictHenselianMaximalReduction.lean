import Langlands.GroupScheme.Torus.LocalMaximalPropagation
import Langlands.GroupScheme.Torus.RelativeLiftingStatement
import Langlands.GroupScheme.Torus.StrictHenselianMaximalStatement
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof

/-! # Split maximal tori over strictly Henselian local rings, from lifting and sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Separable closedness transfers along a ring isomorphism of fields. -/
theorem isSepClosed_of_ringEquiv {k K : Type*} [Field k] [Field K] (e : k ≃+* K)
    [IsSepClosed k] : IsSepClosed K := by
  apply IsSepClosed.of_exists_root
  intro p hmon hirr hsep
  have hdeg : (p.map e.symm.toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hirr)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (p.map e.symm.toRingHom) hdeg hsep.map
  refine ⟨e x, ?_⟩
  rw [Polynomial.IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hdeg hirr hsep hmon
  induction p using Polynomial.induction_on <;> simp_all

/-- The scheme-theoretic residue field at the closed point of a local spectrum is
separably closed when the ring-theoretic residue field is. -/
theorem isSepClosed_residueField_closedPoint (R : Type u) [CommRing R] [IsLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] :
    IsSepClosed ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) := by
  let e₁ : IsLocalRing.ResidueField R ≃+* (IsLocalRing.maximalIdeal R).ResidueField :=
    RingEquiv.ofBijective (algebraMap (R ⧸ IsLocalRing.maximalIdeal R) _)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  let e₂ := (Scheme.Spec.residueFieldIso (CommRingCat.of R)
    (IsLocalRing.closedPoint R)).commRingCatIsoToRingEquiv
  exact isSepClosed_of_ringEquiv (e₁.trans e₂.symm)

/-- A smooth affine group over a separably closed field has a split maximal torus. -/
theorem exists_isMaximalTorus_isSplitTorus_of_isSepClosed {k : Type u} [Field k]
    [IsSepClosed k] (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom]
    [IsAffineHom G.X.hom] :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalTorus i ∧ IsSplitTorus T.toGrp := by
  obtain ⟨T, i, hi⟩ := TorusExistence.exists_isMaximalTorus G
  exact ⟨T, i, hi, SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
    Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning T.toGrp hi.1⟩

/-- Maximality is preserved by replacing an inclusion with an isomorphic one. -/
theorem IsMaximalTorus.of_eq_iso_comp_comp_iso {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {G G' : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalTorus i) (A : T'.toGrp ≅ T.toGrp) (B : G ≅ G') {j : T'.toGrp ⟶ G'}
    (h : j = A.hom ≫ i ≫ B.hom) : IsMaximalTorus j := by
  subst h
  exact (hi.comp_iso B).iso_comp A

/-- Pullback composition is natural in the supplied homomorphism. -/
theorem baseChangeCompIso_hom_naturality {S S' S'' : Scheme.{u}}
    (a : S' ⟶ S) (b : S'' ⟶ S') {H K : GroupScheme S} (i : H ⟶ K) :
    (baseChange (b ≫ a)).map i ≫ (baseChangeCompIso a b K).hom =
      (baseChangeCompIso a b H).hom ≫ (baseChange b).map ((baseChange a).map i) :=
  ((Functor.mapGrpNatIso (Over.pullbackComp b a)) ≪≫ Functor.mapGrpCompIso).hom.naturality i

/-- Pulling back along a section of `p` returns the original group. -/
def sectionPullbackIso {S U : Scheme.{u}} (p : U ⟶ S) (σ : S ⟶ U) (hσ : σ ≫ p = 𝟙 S)
    (G : GroupScheme S) : (baseChange σ).obj ((baseChange p).obj G) ≅ G :=
  (baseChangeCompIso p σ G).symm ≪≫
    eqToIso (congrArg (fun f => (baseChange f).obj G) hσ) ≪≫ baseChangeIdIso G

/-- After a further base change `c`, the pullback of an inclusion along a section is
isomorphic to the pullback along the composite `c ≫ σ`. -/
theorem baseChange_map_sectionPullback {S U S₀ : Scheme.{u}} (p : U ⟶ S) (σ : S ⟶ U)
    (hσ : σ ≫ p = 𝟙 S) (c : S₀ ⟶ S) {G : GroupScheme S} {T : GroupScheme U}
    (i : T ⟶ (baseChange p).obj G) :
    ∃ (A : (baseChange c).obj ((baseChange σ).obj T) ≅ (baseChange (c ≫ σ)).obj T)
      (B : (baseChange (c ≫ σ)).obj ((baseChange p).obj G) ≅ (baseChange c).obj G),
      (baseChange c).map ((baseChange σ).map i ≫ (sectionPullbackIso p σ hσ G).hom) =
        A.hom ≫ (baseChange (c ≫ σ)).map i ≫ B.hom := by
  refine ⟨(baseChangeCompIso σ c T).symm,
    baseChangeCompIso σ c _ ≪≫ (baseChange c).mapIso (sectionPullbackIso p σ hσ G), ?_⟩
  have h := baseChangeCompIso_hom_naturality σ c i
  simp only [Functor.map_comp, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [reassoc_of% h, Iso.inv_hom_id_assoc]

/-- Relative lifting of split tori and pointed sections of etale morphisms over
Henselian local rings together imply the existence of a closed split torus that is
maximal on every residue fibre over a strictly Henselian local ring. -/
def StrictHenselianSplitMaximalTorusReductionStatement : Prop :=
  RelativeSplitTorusLiftingStatement.{u} →
  (∀ (R : Type u) [CommRing R] [HenselianLocalRing R] (U : Scheme.{u})
    (p : U ⟶ Spec (CommRingCat.of R)), Etale p →
    ∀ (b : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶ U),
      b ≫ p = (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) →
      ∃ σ : Spec (CommRingCat.of R) ⟶ U, σ ≫ p = 𝟙 _ ∧
        (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) ≫ σ = b) →
  StrictHenselianSplitMaximalTorusStatement.{u}

/-- The reduction of the strictly Henselian split maximal torus statement to relative
lifting and Henselian sections. -/
theorem strictHenselianSplitMaximalTorusReduction :
    StrictHenselianSplitMaximalTorusReductionStatement.{u} := by
  intro hLift hSect R _ _ _ G hG
  let := hG.smooth
  let := hG.isAffineHom
  have hsep := isSepClosed_residueField_closedPoint R
  let f₀ := (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)
  let : Smooth ((baseChange f₀).obj G).X.hom :=
    inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom f₀))
  let : IsAffineHom ((baseChange f₀).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom f₀))
  obtain ⟨T₀, i₀, hi₀, hT₀⟩ :=
    exists_isMaximalTorus_isSplitTorus_of_isSepClosed
      (k := (Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
      ((baseChange f₀).obj G)
  obtain ⟨U, p, hp, b, hb, T, hT, i, hic, e, he⟩ :=
    hLift (Spec (CommRingCat.of R)) G (IsLocalRing.closedPoint R) T₀.toGrp hT₀ i₀ hi₀.2.1
  obtain ⟨σ, hσ, hσb⟩ := hSect R U p hp b hb
  subst hσb
  obtain ⟨I, hI, ⟨e'⟩⟩ := hT.baseChange σ
  let ic : (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I).toGrp ⟶ G :=
    e'.inv ≫ (baseChange σ).map i ≫ (sectionPullbackIso p σ hσ G).hom
  have hclosed : IsClosedSubgroup ic :=
    ((IsClosedSubgroup.baseChange σ (f := i) hic).comp_iso
      (sectionPullbackIso p σ hσ G)).iso_comp e'.symm
  have hsplit : IsSplitTorus
      (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I).toGrp :=
    ⟨I, hI, ⟨Iso.refl _⟩⟩
  refine ⟨_, ic, hsplit, hclosed,
    localClosedFibreMaximalPropagation R G hG _ ic hsplit hclosed ?_⟩
  have he' : (baseChange (f₀ ≫ σ)).map i = e.hom ≫ i₀ ≫
      (eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).inv ≫
        (baseChangeCompIso p (f₀ ≫ σ) G).hom := by
    rw [← reassoc_of% he]
    simp
    rfl
  obtain ⟨A, B, hAB⟩ := baseChange_map_sectionPullback p σ hσ f₀ i
  refine IsMaximalTorus.of_eq_iso_comp_comp_iso hi₀
    ((baseChange f₀).mapIso e'.symm ≪≫ A ≪≫ e)
    ((eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).symm ≪≫
      baseChangeCompIso p (f₀ ≫ σ) G ≪≫ B) ?_
  change (baseChange f₀).map (e'.inv ≫ ((baseChange σ).map i ≫
    (sectionPullbackIso p σ hσ G).hom)) = _
  rw [Functor.map_comp, hAB, he']
  simp

end Langlands.GroupScheme
