import Langlands.GroupScheme.Torus.HenselianNormalizerLifting
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof

/-! # Integral conjugacy of split tori with maximal residue fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace splitTorus

/-- A specified isomorphism between two coordinate tori over a field extends
with its exact integral character coordinates over any base scheme. -/
theorem exists_fieldIsomorphismExtension
    (k : Type u) [Field k] (I J : Type u) [Fintype I] [Fintype J]
    (S : Scheme.{u}) (b : Spec (CommRingCat.of k) ⟶ S)
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) J) :
    ∃ e : commGroupScheme S I ≅ commGroupScheme S J,
      (commBaseChangeIso b I).inv ≫ (CommGroupScheme.baseChange b).map e.hom ≫
        (commBaseChangeIso b J).hom = Additive.ofMul c.hom := by
  classical
  let e : commGroupScheme S I ≅ commGroupScheme S J :=
    { hom := exponentHom S I J (characterMap I J c.hom)
      inv := exponentHom S J I (characterMap J I c.inv)
      hom_inv_id := by
        rw [exponentHom_comp, ← characterMap_comp, c.hom_inv_id,
          characterMap_id, exponentHom_id]
      inv_hom_id := by
        rw [exponentHom_comp, ← characterMap_comp, c.inv_hom_id,
          characterMap_id, exponentHom_id] }
  refine ⟨e, ?_⟩
  change (commBaseChangeIso b I).inv ≫
    (CommGroupScheme.baseChange b).map
      (exponentHom S I J (characterMap I J c.hom)) ≫
        (commBaseChangeIso b J).hom = _
  rw [← exponentHom_baseChange, Iso.inv_hom_id_assoc]
  exact exponentHom_characterMap k I J c.hom

end splitTorus

/-- Every actual isomorphism between field fibres of two split tori extends
between the original tori and recovers the entire specified isomorphism. -/
theorem IsSplitTorus.isomorphism_fieldBaseChange_surjective
    {S : Scheme.{u}} {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) {T₁ T₂ : CommGroupScheme S}
    (hT₁ : IsSplitTorus T₁.toGrp) (hT₂ : IsSplitTorus T₂.toGrp) :
    Function.Surjective
      (fun e : T₁ ≅ T₂ => (CommGroupScheme.baseChange b).mapIso e) := by
  classical
  obtain ⟨I, hI, ⟨e₁⟩⟩ := hT₁
  obtain ⟨J, hJ, ⟨e₂⟩⟩ := hT₂
  let : Finite I := hI
  let : Finite J := hJ
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  let a₁ : T₁ ≅ splitTorus.commGroupScheme S I := CommGroupScheme.isoOfGroupIso e₁
  let a₂ : T₂ ≅ splitTorus.commGroupScheme S J := CommGroupScheme.isoOfGroupIso e₂
  let B := CommGroupScheme.baseChange b
  let d₁ := splitTorus.commBaseChangeIso b I
  let d₂ := splitTorus.commBaseChangeIso b J
  let q₁ := B.mapIso a₁ ≪≫ d₁
  let q₂ := B.mapIso a₂ ≪≫ d₂
  intro e₀
  let c := q₁.symm ≪≫ e₀ ≪≫ q₂
  let cG : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) J :=
    { hom := CommGroupScheme.groupHom c.hom
      inv := CommGroupScheme.groupHom c.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom c.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom c.inv_hom_id }
  obtain ⟨c₀, hc₀⟩ := splitTorus.exists_fieldIsomorphismExtension k I J S b cG
  refine ⟨a₁ ≪≫ c₀ ≪≫ a₂.symm, ?_⟩
  apply Iso.ext
  change B.map (a₁.hom ≫ c₀.hom ≫ a₂.inv) = e₀.hom
  have hc : d₁.inv ≫ B.map c₀.hom ≫ d₂.hom = c.hom := hc₀
  have hc' : B.map c₀.hom = d₁.hom ≫ c.hom ≫ d₂.inv := by
    rw [← hc]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp, hc']
  dsimp only [c, q₁, q₂, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [B.map_id, Category.id_comp, ← B.map_comp, a₂.hom_inv_id,
    B.map_id, Category.comp_id]

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {H G : GroupScheme S}
    {j₁ j₂ : H ⟶ G} {g : Over.mk (𝟙 S) ⟶ G.X}

/-- For a section, the all-test transporter relation is precisely an equality
of the actual conjugated homomorphisms, with the transporter orientation. -/
theorem isTransporter_iff_conjugation_eq :
    IsTransporter j₂ j₁ g ↔ j₁ ≫ (G.innerIso g).hom = j₂ := by
  constructor
  · intro hg
    apply hom_ext_points
    intro V t
    rw [Grp.comp_hom_hom, ← Category.assoc, G.comp_innerIso_hom]
    have h := hg V (Over.homMk V.hom (by simp)) t
    change (t ≫ j₂.hom.hom) * G.constantPoint g V =
      G.constantPoint g V * (t ≫ j₁.hom.hom) at h
    exact mul_inv_eq_iff_eq_mul.mpr h.symm
  · intro hg V a t
    have h := congrArg (fun f : H ⟶ G => t ≫ f.hom.hom) hg
    rw [Grp.comp_hom_hom, ← Category.assoc, G.comp_innerIso_hom] at h
    have hc : G.constantPoint g V = a ≫ g := by
      unfold GroupScheme.constantPoint
      congr 1
      apply Over.OverMorphism.ext
      change V.hom = a.left
      have ha := Over.w a
      change a.left ≫ 𝟙 S = V.hom at ha
      exact ha.symm.trans (Category.comp_id _)
    rw [hc] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm

end PointwiseSchemeAction

section Henselian

variable {R k : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
    {T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of R))}
    (j₁ : T₁.toGrp ⟶ G) (j₂ : T₂.toGrp ⟶ G)

/-- A prescribed residue conjugacy between two split integral tori lifts,
recovering both its point and its actual source isomorphism exactly. -/
theorem exists_henselian_splitTorus_conjugacy_lift
    (hT₁ : IsSplitTorus T₁.toGrp) (hT₂ : IsSplitTorus T₂.toGrp)
    (hG : Smooth G.X.hom) (hk : Function.Surjective (algebraMap R k))
    (g₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      ((baseChange (Spec.algebraMap R k)).obj G).X)
    (e₀ : (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₁ ≅
      (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₂)
    (h₀ : (baseChange (Spec.algebraMap R k)).map j₁ ≫
        (((baseChange (Spec.algebraMap R k)).obj G).innerIso g₀).hom =
      CommGroupScheme.groupHom e₀.hom ≫ (baseChange (Spec.algebraMap R k)).map j₂) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X) (e : T₁ ≅ T₂),
      j₁ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j₂ ∧
        baseChangeSectionHom (Spec.algebraMap R k) G g = g₀ ∧
        (CommGroupScheme.baseChange (Spec.algebraMap R k)).mapIso e = e₀ := by
  let b := Spec.algebraMap R k
  obtain ⟨e, he⟩ := hT₁.isomorphism_fieldBaseChange_surjective b hT₂ e₀
  have h₀' : (baseChange b).map j₁ ≫ (((baseChange b).obj G).innerIso g₀).hom =
      (baseChange b).map (CommGroupScheme.groupHom e.hom ≫ j₂) := by
    rw [Functor.map_comp]
    change (baseChange b).map j₁ ≫ (((baseChange b).obj G).innerIso g₀).hom =
      CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).mapIso e).hom ≫
        (baseChange b).map j₂
    have heq := congrArg (fun σ : (CommGroupScheme.baseChange b).obj T₁ ≅
        (CommGroupScheme.baseChange b).obj T₂ =>
      CommGroupScheme.groupHom σ.hom ≫ (baseChange b).map j₂) he
    exact h₀.trans heq.symm
  have ht := PointwiseSchemeAction.isTransporter_iff_conjugation_eq.mpr h₀'
  let c : Over.mk b ⟶ (Over.map b).obj (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    Over.homMk (𝟙 _) (by simp)
  obtain ⟨g, hg, hrec⟩ := PointwiseSchemeAction.exists_henselian_transporter_of_split
    (CommGroupScheme.groupHom e.hom ≫ j₂) j₁ hT₁ hG hk
    (c ≫ baseChangePointsEquiv b G _ g₀)
    ((ht.baseChangePointsEquiv b).restrict c)
  refine ⟨g, e, PointwiseSchemeAction.isTransporter_iff_conjugation_eq.mp hg, ?_, he⟩
  apply (baseChangePointsEquiv b G _).injective
  rw [baseChangePointsEquiv_baseChangeSectionHom]
  apply Over.OverMorphism.ext
  have hh := congrArg Over.Hom.left hrec
  change b ≫ g.left = (𝟙 (Spec (CommRingCat.of k))) ≫
    g₀.left ≫ Limits.pullback.fst G.X.hom b at hh
  change b ≫ g.left = g₀.left ≫ Limits.pullback.fst G.X.hom b
  simpa only [Category.id_comp] using hh

/-- Two split integral tori with maximal residue fibres in a connected
smooth residue group over an algebraically closed field are integrally conjugate. -/
theorem exists_henselian_splitTorus_conjugacy
    [IsAlgClosed k] [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj G).X.left]
    (hT₁ : IsSplitTorus T₁.toGrp) (hT₂ : IsSplitTorus T₂.toGrp)
    (hG : Smooth G.X.hom) (hk : Function.Surjective (algebraMap R k))
    (hj₁ : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₁)
      ((baseChange (Spec.algebraMap R k)).map j₁))
    (hj₂ : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₂)
      ((baseChange (Spec.algebraMap R k)).map j₂)) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X) (e : T₁ ≅ T₂),
      j₁ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j₂ := by
  let : Smooth G.X.hom := hG
  let : IsAffineHom G.X.hom := isAffineHom_of_isAffine _
  let b := Spec.algebraMap R k
  obtain ⟨g₀, e₀, h₀⟩ := maximalTorusConjugacy k ((baseChange b).obj G)
    ((CommGroupScheme.baseChange b).obj T₁) ((CommGroupScheme.baseChange b).obj T₂)
    ((baseChange b).map j₁) ((baseChange b).map j₂) hj₁ hj₂
  obtain ⟨g, e, he, -, -⟩ := exists_henselian_splitTorus_conjugacy_lift
    j₁ j₂ hT₁ hT₂ hG hk g₀ e₀ h₀
  exact ⟨g, e, he⟩

end Henselian

end Langlands.GroupScheme

namespace Langlands.GroupScheme

/-- Integral conjugacy of supplied split tori whose residue maps are maximal,
over a Henselian local ring with algebraically closed residue field. -/
def HenselianSplitTorusConjugacyStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
    Function.Surjective (algebraMap R k) →
    ∀ (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
      [Smooth G.X.hom]
      [ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj G).X.left]
      (T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of R)))
      (j₁ : T₁.toGrp ⟶ G) (j₂ : T₂.toGrp ⟶ G),
      IsSplitTorus T₁.toGrp → IsSplitTorus T₂.toGrp →
      IsMaximalTorus (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₁)
        ((baseChange (Spec.algebraMap R k)).map j₁) →
      IsMaximalTorus (T := (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T₂)
        ((baseChange (Spec.algebraMap R k)).map j₂) →
      ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X) (e : T₁ ≅ T₂),
        j₁ ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j₂

/-- Residue maximal-torus conjugacy followed by exact Henselian lifting. -/
theorem henselianSplitTorusConjugacy : HenselianSplitTorusConjugacyStatement.{u} := by
  intro R _ _ k _ _ _ hk G _ _ _ T₁ T₂ j₁ j₂ hT₁ hT₂ hj₁ hj₂
  exact exists_henselian_splitTorus_conjugacy j₁ j₂ hT₁ hT₂ inferInstance hk hj₁ hj₂

end Langlands.GroupScheme
