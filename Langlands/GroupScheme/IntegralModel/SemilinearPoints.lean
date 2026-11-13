import Langlands.GroupScheme.IntegralModel.SemilinearModel
import Langlands.GroupScheme.GaloisPointRational
import Mathlib.Tactic.IrreducibleDef

/-! # Integral points of actual coefficient twists -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

/-- Sections are detected after pullback along an epimorphism of bases. -/
theorem baseChangeSectionHom_injective {S : Scheme.{u}} (a : S ⟶ S) [Epi a]
    (H : GroupScheme S) : Function.Injective (baseChangeSectionHom a H) := by
  intro x y h
  apply Over.OverMorphism.ext
  apply (cancel_epi a).mp
  exact (baseChangeSectionHom_fst a H x).symm.trans
    ((congrArg (fun z => z.left ≫ pullback.fst H.X.hom a) h).trans
      (baseChangeSectionHom_fst a H y))

/-- An actual group-scheme isomorphism is injective on rational points. -/
theorem rationalPoints.map_iso_injective {K : Type u} [CommRing K]
    {H J : GroupScheme (Spec (CommRingCat.of K))} (e : H ≅ J) :
    Function.Injective (rationalPoints.map e.hom) := by
  intro x y h
  exact (cancel_mono e.hom.hom.hom).mp h

/-- The inverse group-scheme isomorphism is inverse on rational points. -/
theorem rationalPoints.map_iso_inv_hom {K : Type u} [CommRing K]
    {H J : GroupScheme (Spec (CommRingCat.of K))} (e : H ≅ J)
    (x : rationalPoints J) :
    rationalPoints.map e.hom (rationalPoints.map e.inv x) = x := by
  simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
    Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

namespace Descent

/-- The projection of a twice-pulled section is precomposition by the
composite base map. -/
theorem section_tower_fst {B S V : Scheme.{u}}
    (b : S ⟶ B) (c : V ⟶ S) (H : GroupScheme B)
    (x : Over.mk (𝟙 B) ⟶ H.X) :
    (baseChangeSectionHom c ((baseChange b).obj H)
        (baseChangeSectionHom b H x)).left ≫
        pullback.fst ((baseChange b).obj H).X.hom c ≫
          pullback.fst H.X.hom b = (c ≫ b) ≫ x.left := by
  have hc := baseChangeSectionHom_fst c ((baseChange b).obj H)
    (baseChangeSectionHom b H x)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ pullback.fst H.X.hom b) hc).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => c ≫ z) (baseChangeSectionHom_fst b H x)).trans
          (Category.assoc _ _ _).symm)))

/-- Iterated pullback sections are determined by their original-group
projection. -/
theorem section_ext_pullback_tower {B S V : Scheme.{u}}
    (b : S ⟶ B) (c : V ⟶ S) (H : GroupScheme B)
    {x y : Over.mk (𝟙 V) ⟶ ((baseChange c).obj ((baseChange b).obj H)).X}
    (h : x.left ≫ pullback.fst ((baseChange b).obj H).X.hom c ≫
        pullback.fst H.X.hom b =
      y.left ≫ pullback.fst ((baseChange b).obj H).X.hom c ≫
        pullback.fst H.X.hom b) : x = y := by
  apply (baseChangeBasePointsEquiv c ((baseChange b).obj H)).injective
  apply (baseChangePointsEquiv b H (Over.mk c)).injective
  apply Over.OverMorphism.ext
  simpa only [baseChangePointsEquiv_left, baseChangeBasePointsEquiv_left,
    Category.assoc] using h

/-- The commuting-square comparison carries the two successive pullbacks of
an original section to one another. -/
theorem squareComparison_section {B S U V : Scheme.{u}}
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) (H : GroupScheme B)
    (x : Over.mk (𝟙 B) ⟶ H.X) :
    baseChangeSectionHom c ((baseChange b).obj H)
        (baseChangeSectionHom b H x) ≫
          (squareComparison b c d e h H).hom.hom.hom =
      baseChangeSectionHom e ((baseChange d).obj H)
        (baseChangeSectionHom d H x) := by
  apply section_ext_pullback_tower d e H
  simp only [Over.comp_left, Category.assoc, squareComparison_hom_fst_fst]
  exact (section_tower_fst b c H x).trans
    ((congrArg (fun z => z ≫ x.left) h).trans
      (section_tower_fst d e H x).symm)

end Descent

/-- The canonical descent comparison transports a section by
precomposition on its original-group projection. -/
theorem descentBaseChangeIso_section_fst {B S : Scheme.{u}}
    (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
    (H : GroupScheme B)
    (x : Over.mk (𝟙 S) ⟶ ((baseChange b).obj H).X) :
    ((baseChangeSectionHom a ((baseChange b).obj H) x) ≫
        (descentBaseChangeIso b a ha H).hom.hom.hom).left ≫
          pullback.fst H.X.hom b =
      a ≫ x.left ≫ pullback.fst H.X.hom b := by
  simp only [Over.comp_left, Category.assoc, descentBaseChangeIso_hom_fst]
  have hx :
      (baseChangeSectionHom a ((baseChange b).obj H) x).left ≫
          pullback.fst (pullback.snd H.X.hom b) a = a ≫ x.left :=
    baseChangeSectionHom_fst a ((baseChange b).obj H) x
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ pullback.fst H.X.hom b) hx).trans
      (Category.assoc _ _ _))

namespace GaloisPointComparison

/-- The actual canonical generic descent isomorphism, with the pullback
objects exposed in the group-scheme base-change convention. -/
irreducible_def galoisDescentIso
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k))) (σ : L ≃ₐ[k] L) :
    (baseChange (galoisBaseMap k L σ)).obj (baseChanged k L G) ≅
      baseChanged k L G :=
  descentBaseChangeIso (baseMap k L) (galoisBaseMap k L σ)
    (galoisBaseMap_over k L σ) G

/-- Inverse coefficient actions cancel on the existing rational-point
carriers. -/
theorem rationalConjugate_symm_apply
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k))) (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    rationalConjugate k L G σ (rationalConjugate k L G σ.symm x) = x := by
  rw [← rationalConjugate_mul]
  change rationalConjugate k L G (σ * σ⁻¹) x = x
  rw [mul_inv_cancel, rationalConjugate_one]

/-- Canonical geometric semilinear transport on a pulled-back rational
section is exactly the existing coefficient Galois action. -/
theorem rationalConjugate_eq_transport
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k))) (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    rationalPoints.map
        (descentBaseChangeIso (baseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G).hom
        (baseChangeSectionHom (galoisBaseMap k L σ) (baseChanged k L G) x) =
      rationalConjugate k L G σ x := by
  apply (baseChangeCoeffEquiv k L G).injective
  rw [baseChangeCoeffEquiv_rationalConjugate]
  apply Over.OverMorphism.ext
  rw [baseChangeCoeffEquiv_left, rationalPoints.map_apply]
  exact descentBaseChangeIso_section_fst (baseMap k L) (galoisBaseMap k L σ)
    (galoisBaseMap_over k L σ) G x

end GaloisPointComparison

namespace IntegralModel

variable {R L : Type u} [CommRing R] [IsDomain R] [Field L]
  [Algebra R L] [IsFractionRing R L]
  {H : GroupScheme (Spec (CommRingCat.of L))}
  (N : IntegralModel R L H)
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (v : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L))
  (hvc : v ≫ Spec.algebraMap R L = Spec.algebraMap R L ≫ a)

/-- An invertible coefficient change identifies the actual integral
sections of the original model and its twist. -/
def twistIntegralSectionsEquiv [IsIso a] :
    N.integralSections ≃* (N.twist a v hvc).integralSections :=
  MulEquiv.ofBijective (baseChangeSectionHom a N.group)
    ⟨baseChangeSectionHom_injective a N.group,
      baseChangeSectionHom_surjective a N.group⟩

/-- Generic evaluation of a pulled-back integral section is its pulled-back
generic evaluation, using the actual square comparison of the twist. -/
theorem twist_integralPointMap (x : N.integralSections) :
    (N.twist a v hvc).integralPointMap (baseChangeSectionHom a N.group x) =
      baseChangeSectionHom v H (N.integralPointMap x) := by
  change
    baseChangeSectionHom (Spec.algebraMap R L) ((GroupScheme.baseChange a).obj N.group)
        (baseChangeSectionHom a N.group x) ≫
          (Descent.squareComparison (Spec.algebraMap R L) v a (Spec.algebraMap R L)
            hvc N.group).inv.hom.hom ≫
              ((GroupScheme.baseChange v).map N.genericIso.hom).hom.hom =
      baseChangeSectionHom v H
        (baseChangeSectionHom (Spec.algebraMap R L) N.group x ≫
          N.genericIso.hom.hom.hom)
  rw [baseChangeSectionHom_naturality]
  have hsec :
      baseChangeSectionHom (Spec.algebraMap R L) ((GroupScheme.baseChange a).obj N.group)
          (baseChangeSectionHom a N.group x) ≫
            (Descent.squareComparison (Spec.algebraMap R L) v a (Spec.algebraMap R L)
              hvc N.group).inv.hom.hom =
        baseChangeSectionHom v ((GroupScheme.baseChange (Spec.algebraMap R L)).obj N.group)
          (baseChangeSectionHom (Spec.algebraMap R L) N.group x) := by
    apply (cancel_mono
      (Descent.squareComparison (Spec.algebraMap R L) v a (Spec.algebraMap R L)
        hvc N.group).hom.hom.hom).mp
    have hi := congrArg (fun f => f.hom.hom)
      (Descent.squareComparison (Spec.algebraMap R L) v a (Spec.algebraMap R L)
        hvc N.group).inv_hom_id
    change
      (Descent.squareComparison (Spec.algebraMap R L) v a (Spec.algebraMap R L)
          hvc N.group).inv.hom.hom ≫
          (Descent.squareComparison (Spec.algebraMap R L) v a (Spec.algebraMap R L)
            hvc N.group).hom.hom.hom = 𝟙 _ at hi
    rw [Category.assoc, hi, Category.comp_id]
    exact (Descent.squareComparison_section (Spec.algebraMap R L) v a
      (Spec.algebraMap R L) hvc N.group x).symm
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ ((GroupScheme.baseChange v).map N.genericIso.hom).hom.hom) hsec)

private theorem range_transport {A B C D : Type u}
    (p : A → B) (q : C → D) (t : A → C) (f : D → B) (s : B → B)
    (ht : Function.Surjective t)
    (htransport : ∀ x, f (q (t x)) = s (p x))
    (hstable : ∀ g ∈ Set.range p, s g ∈ Set.range p)
    {g : D} (hg : g ∈ Set.range q) : f g ∈ Set.range p := by
  obtain ⟨y, hy⟩ := hg
  obtain ⟨x, hx⟩ := ht y
  have h := htransport x
  rw [hx, hy] at h
  exact h.symm ▸ hstable (p x) ⟨x, rfl⟩

private theorem range_inverse_transport {A B C D : Type u}
    (p : A → B) (q : C → D) (t : A → C) (f : D → B) (f' : B → D)
    (s s' : B → B)
    (hf : Function.Injective f) (hfi : ∀ g, f (f' g) = g)
    (htransport : ∀ x, f (q (t x)) = s (p x))
    (hss : ∀ g, s (s' g) = g)
    (hstable : ∀ g ∈ Set.range p, s' g ∈ Set.range p)
    {g : B} (hg : g ∈ Set.range p) : f' g ∈ Set.range q := by
  obtain ⟨x, hx⟩ := hstable g hg
  refine ⟨t x, hf ?_⟩
  exact (htransport x).trans ((congrArg s hx).trans ((hss g).trans (hfi g).symm))

/-- An exact section transport and an inverse point action give the inverse
integral-point inclusion for an arbitrary generic isomorphism. -/
theorem inv_map_mem_integralPoints_of_section_transport
    {J : GroupScheme (Spec (CommRingCat.of L))}
    (Q : IntegralModel R L J) (e : J ≅ H)
    (t : N.integralSections → Q.integralSections)
    (s s' : rationalPoints H → rationalPoints H)
    (htransport : ∀ x, rationalPoints.map e.hom (Q.integralPointMap (t x)) =
      s (N.integralPointMap x))
    (hss : ∀ g, s (s' g) = g)
    (hstable : ∀ g ∈ N.integralPoints, s' g ∈ N.integralPoints)
    {g : rationalPoints H} (hg : g ∈ N.integralPoints) :
    rationalPoints.map e.inv g ∈ Q.integralPoints :=
  range_inverse_transport N.integralPointMap Q.integralPointMap t
    (rationalPoints.map e.hom) (rationalPoints.map e.inv) s s'
    (rationalPoints.map_iso_injective e) (rationalPoints.map_iso_inv_hom e)
    htransport hss hstable hg

section GaloisPoints

open GaloisPointComparison

variable (k : Type u) [Field k] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (P : IntegralModel R L (baseChanged k L G))
  (σ : L ≃ₐ[k] L)
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (hσ : galoisBaseMap k L σ ≫ Spec.algebraMap R L = Spec.algebraMap R L ≫ a)

/-- Under the canonical generic descent identification, the twist evaluation
of an integral section is the coefficient conjugate of its evaluation. -/
theorem twist_integralPointMap_galois (x : P.integralSections) :
    rationalPoints.map
        (descentBaseChangeIso (baseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G).hom
        ((P.twist a (galoisBaseMap k L σ) hσ).integralPointMap
          (baseChangeSectionHom a P.group x)) =
      rationalConjugate k L G σ (P.integralPointMap x) := by
  rw [twist_integralPointMap]
  exact rationalConjugate_eq_transport k L G σ (P.integralPointMap x)

/-- Stability under a coefficient automorphism supplies the forward
integral-point inclusion for its actual twist. -/
theorem galoisTwist_map_mem_integralPoints [IsIso a]
    (hstable : ∀ g ∈ P.integralPoints,
      rationalConjugate k L G σ g ∈ P.integralPoints)
    {g : rationalPoints ((GroupScheme.baseChange (galoisBaseMap k L σ)).obj
      (baseChanged k L G))}
    (hg : g ∈ (P.twist a (galoisBaseMap k L σ) hσ).integralPoints) :
    rationalPoints.map
        (descentBaseChangeIso (baseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G).hom g ∈ P.integralPoints := by
  exact range_transport P.integralPointMap
    (P.twist a (galoisBaseMap k L σ) hσ).integralPointMap
    (baseChangeSectionHom a P.group)
    (rationalPoints.map (descentBaseChangeIso (baseMap k L) (galoisBaseMap k L σ)
      (galoisBaseMap_over k L σ) G).hom)
    (rationalConjugate k L G σ)
    (baseChangeSectionHom_surjective a P.group)
    (twist_integralPointMap_galois k G P σ a hσ) hstable hg

end GaloisPoints

end IntegralModel
end Langlands.GroupScheme
