import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.Derived.NormalityTransfer
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Isomorphism invariance and geometric normality of the torus envelope -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G H K : GroupScheme (Spec (CommRingCat.of k))}

/-- Containing all closed ground-field tori is preserved by inverse image under
an ambient group-scheme isomorphism. -/
theorem SubgroupFunctor.ContainsTori.comap_iso {F : SubgroupFunctor H}
    (hF : F.ContainsTori) (e : G ≅ H) : (F.comap e.hom).ContainsTori := by
  intro T i hT hi U x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have h := hF T (i ≫ e.hom) hT (hi.comp_iso e) U
    (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)
  simpa only [SubgroupFunctor.mem_comap, Grp.comp_hom_hom, Category.assoc] using h

private theorem closedTorusEnvelope_le_comap_iso (e : G ≅ H) :
    closedTorusEnvelope G ≤ (closedTorusEnvelope H).comap e.hom := by
  intro U x hx K j hj ht
  have he : SubgroupFunctor.range (j ≫ e.inv) =
      (SubgroupFunctor.range j).comap e.hom := by
    simpa only [Iso.symm_hom, Iso.symm_inv] using
      SubgroupFunctor.range_comp_iso j e.symm
  have ht' : (SubgroupFunctor.range (j ≫ e.inv)).ContainsTori := by
    rw [he]
    exact ht.comap_iso e
  have h := closedTorusEnvelope_le (j ≫ e.inv) (hj.comp_iso e.symm) ht' U hx
  rwa [he] at h

/-- The fixed closed torus envelope is invariant under every ambient
group-scheme isomorphism, on every relative scheme test. -/
theorem closedTorusEnvelope_eq_comap_iso (e : G ≅ H) :
    closedTorusEnvelope G = (closedTorusEnvelope H).comap e.hom := by
  apply le_antisymm (closedTorusEnvelope_le_comap_iso e)
  have h := SubgroupFunctor.comap_mono (f := e.hom)
    (closedTorusEnvelope_le_comap_iso e.symm)
  simpa only [Iso.symm_hom, ← SubgroupFunctor.comap_comp,
    e.hom_inv_id, SubgroupFunctor.comap_id] using h

namespace TorusGeneratedEnvelope

variable (D : TorusGeneratedEnvelope G)

/-- Transport an actual representative of the fixed envelope along an
ambient group-scheme isomorphism. -/
def transport (e : G ≅ H) : TorusGeneratedEnvelope H where
  group := D.group
  inclusion := D.inclusion ≫ e.hom
  closed := D.closed.comp_iso e
  represents := by
    have he : closedTorusEnvelope H = (closedTorusEnvelope G).comap e.inv := by
      simpa only [Iso.symm_hom] using closedTorusEnvelope_eq_comap_iso e.symm
    rw [he]
    exact D.represents.comp_iso e

/-- The actual isomorphism between envelope representatives induced by an
isomorphism of their ambient groups. -/
def isoOver (D' : TorusGeneratedEnvelope H) (e : G ≅ H) : D.group ≅ D'.group :=
  (D.transport e).iso D'

theorem isoOver_hom_comp (D' : TorusGeneratedEnvelope H) (e : G ≅ H) :
    (D.isoOver D' e).hom ≫ D'.inclusion = D.inclusion ≫ e.hom :=
  (D.transport e).iso_hom_comp D'

/-- Every rational ambient point normalizes the full envelope functor, after
every refinement of the rational base test. -/
theorem rational_mem_normalizer
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    g ∈ (SubgroupFunctor.range D.inclusion).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  rw [D.represents.2]
  intro V a x hx
  constructor
  · have h := (closedTorusEnvelope_eq_comap_iso (G.innerIso g)).le V hx
    change x ≫ (G.innerIso g).hom.hom.hom ∈ (closedTorusEnvelope G).carrier V at h
    simpa only [comp_innerIso_hom, comp_eq_constantPoint a g] using h
  · have h := (closedTorusEnvelope_eq_comap_iso (G.innerIso g⁻¹)).le V hx
    change x ≫ (G.innerIso g⁻¹).hom.hom.hom ∈ (closedTorusEnvelope G).carrier V at h
    simpa only [comp_innerIso_hom, constantPoint_inv, inv_inv,
      comp_eq_constantPoint a g] using h

/-- Over an algebraically closed field, a represented fixed torus envelope
in a reduced affine group locally of finite type is normal on every test.
No reducedness hypothesis on the envelope or its normalizer is required. -/
theorem isNormal_of_isAlgClosed [IsAlgClosed k]
    [IsReduced G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    (SubgroupFunctor.range D.inclusion).IsNormal := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, n, hn, hr⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range D.inclusion D.closed).1
  have hle : SubgroupFunctor.range (𝟙 G) ≤ SubgroupFunctor.range n := by
    apply SubgroupFunctor.range_le_of_algClosed_points hn
    intro g _
    rw [hr.2]
    exact D.rational_mem_normalizer g
  apply SubgroupFunctor.isNormal_of_normalizer_eq_top
  apply le_antisymm
  · intro V g _
    exact Subgroup.mem_top _
  intro V g _
  rw [← hr.2]
  exact hle V (SubgroupFunctor.mem_range.mpr ⟨g, by
    simp only [Grp.id_hom_hom, Category.comp_id]⟩)

/-- In particular, geometric envelope normality holds for every smooth
affine ambient group, without a connectedness hypothesis. -/
theorem isNormal_of_smooth_isAlgClosed [IsAlgClosed k]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    (SubgroupFunctor.range D.inclusion).IsNormal := by
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  exact D.isNormal_of_isAlgClosed

/-- Full normality of the envelope descends through an fpqc base change.
The proof descends containment in the actual closed normalizer. -/
theorem isNormal_of_baseChange {S' : Scheme.{u}}
    (b : S' ⟶ Spec (CommRingCat.of k))
    [QuasiCompact b] [Flat b] [Surjective b] [IsAffineHom G.X.hom]
    (h : ((SubgroupFunctor.range D.inclusion).baseChange b).IsNormal) :
    (SubgroupFunctor.range D.inclusion).IsNormal := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, n, hn, hr⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range D.inclusion D.closed).1
  let : Mono n.hom.hom := hr.1
  have hle : (⊤ : SubgroupFunctor G) ≤ SubgroupFunctor.range n := by
    apply SubgroupFunctor.le_range_of_baseChange_le b n
    rw [SubgroupFunctor.top_baseChange, hr.2,
      SubgroupFunctor.normalizer_baseChange,
      SubgroupFunctor.normalizer_eq_top_of_isNormal h]
  apply SubgroupFunctor.isNormal_of_normalizer_eq_top
  rw [← hr.2]
  exact le_antisymm (fun _ _ _ => Subgroup.mem_top _) hle

/-- If the fixed envelope commutes with a supplied extension of the field,
the actual base-changed inclusion represents the envelope there. -/
def baseChangeOfEnvelopeEquality {l : Type u} [Field l]
    (b : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k))
    (h : (closedTorusEnvelope G).baseChange b =
      closedTorusEnvelope ((GroupScheme.baseChange b).obj G)) :
    TorusGeneratedEnvelope ((GroupScheme.baseChange b).obj G) where
  group := (GroupScheme.baseChange b).obj D.group
  inclusion := (GroupScheme.baseChange b).map D.inclusion
  closed := D.closed.baseChange b
  represents := by
    rw [← h]
    exact D.represents.baseChange b

/-- Algebraic-closure compatibility of the fixed envelope suffices for full
normality over the original field. The compatibility is an explicit input. -/
theorem isNormal_of_algebraicClosure_envelope_eq
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (h : (closedTorusEnvelope G).baseChange (toAlgebraicClosure k) =
      closedTorusEnvelope ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)) :
    (SubgroupFunctor.range D.inclusion).IsNormal := by
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective (toAlgebraicClosure k) := hs
  let : Flat (toAlgebraicClosure k) := hf
  let : QuasiCompact (toAlgebraicClosure k) := hq
  let : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  apply D.isNormal_of_baseChange (toAlgebraicClosure k)
  rw [← SubgroupFunctor.range_baseChangeHom]
  exact (D.baseChangeOfEnvelopeEquality (toAlgebraicClosure k) h).isNormal_of_smooth_isAlgClosed

end TorusGeneratedEnvelope

end Langlands.GroupScheme
