import Langlands.GroupScheme.Descent.FiniteUnramifiedFieldFactorization
import Langlands.GroupScheme.Descent.FiniteStageIso
import Langlands.GroupScheme.EmbeddingEvaluationCoherence

/-! # Specified isomorphisms at finite unramified Galois stages -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

open EmbeddingProduct
open Langlands.AlgebraicGeometry.Picard

private theorem pullHom_projection {S T U : Scheme.{u}} (q : U ⟶ T)
    {f g : T ⟶ S} {r s : U ⟶ S} (hf : q ≫ f = r) (hg : q ≫ g = s)
    {G H : GroupScheme S}
    (a : (baseChange f).obj G ⟶ (baseChange g).obj H) :
    (pullHom q hf hg a).hom.hom.left ≫ intermediateProjection g s q hg H =
      intermediateProjection f r q hf G ≫ a.hom.hom.left := by
  have hforward : (pullbackComparison g q s hg H).hom.hom.hom.left ≫
      intermediateProjection g s q hg H =
        pullback.fst ((baseChange g).obj H).X.hom q := by
    rw [← pullbackComparison_inv_intermediateProjection]
    change ((pullbackComparison g q s hg H).hom ≫
      (pullbackComparison g q s hg H).inv).hom.hom.left ≫ _ = _
    simp
  simp only [pullHom, Grp.comp_hom_hom, Over.comp_left, Category.assoc, hforward]
  rw [show ((baseChange q).map a).hom.hom.left ≫
      pullback.fst ((baseChange g).obj H).X.hom q =
        pullback.fst ((baseChange f).obj G).X.hom q ≫ a.hom.hom.left from
          pullback.lift_fst _ _ _, ← Category.assoc,
    pullbackComparison_inv_intermediateProjection]

private theorem intermediateProjection_comp {S T U V : Scheme.{u}}
    (f : T ⟶ S) (q : U ⟶ T) (p : V ⟶ U)
    (r : U ⟶ S) (t : V ⟶ S) (k : V ⟶ T)
    (hq : q ≫ f = r) (hp : p ≫ r = t) (hk : k ≫ f = t)
    (h : p ≫ q = k) (G : GroupScheme S) :
    intermediateProjection r t p hp G ≫ intermediateProjection f r q hq G =
      intermediateProjection f t k hk G := by
  apply pullback.hom_ext
  · simp only [Category.assoc, intermediateProjection_fst]
  · simp only [Category.assoc, intermediateProjection_snd]
    rw [← Category.assoc, intermediateProjection_snd, Category.assoc, h]

private theorem pullHom_comp_base {S T U V : Scheme.{u}}
    (f : T ⟶ S) (q : U ⟶ T) (p : V ⟶ U)
    (r : U ⟶ S) (t : V ⟶ S) (k : V ⟶ T)
    (hq : q ≫ f = r) (hp : p ≫ r = t) (hk : k ≫ f = t)
    (h : p ≫ q = k) {G H : GroupScheme S}
    (a : (baseChange f).obj G ⟶ (baseChange f).obj H) :
    pullHom p hp hp (pullHom q hq hq a) = pullHom k hk hk a := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · calc
      _ = (pullHom p hp hp (pullHom q hq hq a)).hom.hom.left ≫
          intermediateProjection r t p hp H ≫ pullback.fst H.X.hom r := by
        rw [intermediateProjection_fst]
      _ = intermediateProjection r t p hp G ≫ (pullHom q hq hq a).hom.hom.left ≫
          pullback.fst H.X.hom r := by rw [← Category.assoc, pullHom_projection, Category.assoc]
      _ = intermediateProjection r t p hp G ≫ (pullHom q hq hq a).hom.hom.left ≫
          intermediateProjection f r q hq H ≫ pullback.fst H.X.hom f := by
        rw [intermediateProjection_fst]
      _ = intermediateProjection r t p hp G ≫ intermediateProjection f r q hq G ≫
          a.hom.hom.left ≫ pullback.fst H.X.hom f := by
        simpa only [Category.assoc] using
          congrArg (fun z => intermediateProjection r t p hp G ≫ z ≫
            pullback.fst H.X.hom f) (pullHom_projection q hq hq a)
      _ = intermediateProjection f t k hk G ≫ a.hom.hom.left ≫
          pullback.fst H.X.hom f := by
        rw [← Category.assoc, intermediateProjection_comp f q p r t k hq hp hk h]
      _ = (pullHom k hk hk a).hom.hom.left ≫ intermediateProjection f t k hk H ≫
          pullback.fst H.X.hom f := by
        simpa only [Category.assoc] using
          congrArg (fun z => z ≫ pullback.fst H.X.hom f)
            (pullHom_projection k hk hk a).symm
      _ = _ := by rw [intermediateProjection_fst]
  · exact (Over.w (pullHom p hp hp (pullHom q hq hq a)).hom.hom).trans
      (Over.w (pullHom k hk hk a).hom.hom).symm

private theorem pullIso_comp_base {S T U V : Scheme.{u}}
    (f : T ⟶ S) (q : U ⟶ T) (p : V ⟶ U)
    (r : U ⟶ S) (t : V ⟶ S) (k : V ⟶ T)
    (hq : q ≫ f = r) (hp : p ≫ r = t) (hk : k ≫ f = t)
    (h : p ≫ q = k) {G H : GroupScheme S}
    (a : (baseChange f).obj G ≅ (baseChange f).obj H) :
    pullIso p hp hp (pullIso q hq hq a) = pullIso k hk hk a := by
  apply Iso.ext
  exact pullHom_comp_base f q p r t k hq hp hk h a.hom

private theorem finiteStage_comparison
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (K : FinIntermediateField k Ω) (G : GroupScheme (Spec (CommRingCat.of k)))
    (h : algebraBaseMap K.1 Ω ≫ algebraBaseMap k K.1 = algebraBaseMap k Ω) :
    FiniteStage.comparison k Ω K G =
      (pullbackComparison _ _ _ h G).symm := by
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · calc
      _ = (baseChangeCone (Ω := Ω) G.X.left G.X.hom).π.app (Opposite.op K) :=
        FiniteStage.comparison_hom_fst k Ω K G
      _ = intermediateProjection (algebraBaseMap k K.1) (algebraBaseMap k Ω)
          (algebraBaseMap K.1 Ω) h G := by
        apply pullback.hom_ext <;> simp [baseChangeCone, intermediateProjection]
      _ = _ := (pullbackComparison_inv_intermediateProjection _ _ _ h G).symm
  · exact (Over.w (FiniteStage.comparison k Ω K G).hom.hom.hom).trans
      (Over.w (pullbackComparison _ _ _ h G).inv.hom.hom).symm

private theorem finiteStage_recovery
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {e : (baseChange (algebraBaseMap k Ω)).obj G ≅
      (baseChange (algebraBaseMap k Ω)).obj H}
    (D : FiniteStage.IsoModel k Ω e)
    (h : algebraBaseMap D.fieldOfDefinition.1 Ω ≫
      algebraBaseMap k D.fieldOfDefinition.1 = algebraBaseMap k Ω) :
    pullIso (algebraBaseMap D.fieldOfDefinition.1 Ω) h h D.iso = e := by
  apply Iso.ext
  have hd := D.recovery
  rw [finiteStage_comparison k Ω D.fieldOfDefinition G h,
    finiteStage_comparison k Ω D.fieldOfDefinition H h] at hd
  apply (cancel_mono (pullbackComparison _ _ _ h H).inv).mp
  simpa only [pullIso_hom, pullHom, Category.assoc, Iso.symm_hom,
    Iso.hom_inv_id, Category.comp_id] using hd

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

variable (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] (hE : E ≤ inertiaFixedField F)

/-- Spectrum of the specified inclusion of intermediate fields. -/
abbrev fieldSpecMap {E E' : IntermediateField F (SeparableClosure F)}
    (h : E ≤ E') :
    Spec (CommRingCat.of E') ⟶ Spec (CommRingCat.of E) :=
  Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[reassoc]
theorem fieldSpecMap_comp {E E' E'' : IntermediateField F (SeparableClosure F)}
    (h : E ≤ E') (h' : E' ≤ E'') :
    fieldSpecMap F h' ≫ fieldSpecMap F h = fieldSpecMap F (h.trans h') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- A finite unramified Galois enlargement recovering a specified isomorphism. -/
structure IsoStage
    {G H : GroupScheme (Spec (CommRingCat.of E))}
    (e : (baseChange (fieldSpecMap F hE)).obj G ≅
      (baseChange (fieldSpecMap F hE)).obj H) where
  field : IntermediateField F (SeparableClosure F)
  finite : FiniteDimensional F field
  galois : IsGalois F field
  contains : E ≤ field
  inertia : field ≤ inertiaFixedField F
  unramified : ArithmeticUnramified F field
  iso : (baseChange (fieldSpecMap F contains)).obj G ≅
    (baseChange (fieldSpecMap F contains)).obj H
  recovery : pullIso (fieldSpecMap F inertia)
    (fieldSpecMap_comp F contains inertia) (fieldSpecMap_comp F contains inertia) iso = e

/-- Specified isomorphisms over the maximal unramified field descend to a
finite unramified Galois enlargement of their original field of definition. -/
theorem nonempty_isoStage
    {G H : GroupScheme (Spec (CommRingCat.of E))}
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (e : (baseChange (fieldSpecMap F hE)).obj G ≅
      (baseChange (fieldSpecMap F hE)).obj H) :
    Nonempty (IsoStage F E hE e) := by
  let U := inertiaFixedField F
  let : Algebra E U := (IntermediateField.inclusion hE).toRingHom.toAlgebra
  let : IsScalarTower F E U := .of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic E U := Algebra.IsAlgebraic.tower_top (K := F) E
  let D := FiniteStage.isoModel E U e
  let K : IntermediateField E U := D.fieldOfDefinition.1
  let eKAlg : Algebra E K := K.toSubalgebra.algebra
  let : SMul E K := eKAlg.toSMul
  let : Module E K := @Algebra.toModule E K _ _ eKAlg
  let : Algebra F K := K.toSubalgebra.algebra'
  let : Algebra K U := K.toAlgebra
  let : IsScalarTower F E K := IntermediateField.isScalarTower K
  let : IsScalarTower F K U := .of_algebraMap_eq' rfl
  let : IsScalarTower E K U := .of_algebraMap_eq' rfl
  let : FiniteDimensional E K := D.fieldOfDefinition.2
  let : FiniteDimensional F K := FiniteDimensional.trans F E K
  let a : K →ₐ[F] U := K.val.restrictScalars F
  let A := fieldFactorization F K a
  have hvalue (x : K) :
      ((A.embedding x : A.field) : SeparableClosure F) = (a x : SeparableClosure F) :=
    congrArg (fun b : K →ₐ[F] U => ((b x : U) : SeparableClosure F)) A.factorization
  have hcontains : E ≤ A.field := by
    intro x hx
    let y : E := ⟨x, hx⟩
    have hy : (A.embedding (algebraMap E K y) : SeparableClosure F) = x :=
      hvalue (algebraMap E K y)
    rw [← hy]
    exact (A.embedding (algebraMap E K y)).property
  let eAAlg : Algebra E A.field :=
    (IntermediateField.inclusion hcontains).toRingHom.toAlgebra
  let : SMul E A.field := eAAlg.toSMul
  let kAAlg : Algebra K A.field := A.embedding.toRingHom.toAlgebra
  let : SMul K A.field := kAAlg.toSMul
  have hEA (y : E) :
      algebraMap E A.field y = algebraMap K A.field (algebraMap E K y) := by
    apply Subtype.ext
    exact (hvalue (algebraMap E K y)).symm
  let : IsScalarTower E K A.field := .of_algebraMap_eq hEA
  have hq : algebraBaseMap K A.field ≫ algebraBaseMap E K =
      fieldSpecMap F hcontains := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq E K A.field]
    rfl
  have hp : fieldSpecMap F A.inertia ≫ fieldSpecMap F hcontains =
      fieldSpecMap F hE := fieldSpecMap_comp F hcontains A.inertia
  have hk : algebraBaseMap K U ≫ algebraBaseMap E K = fieldSpecMap F hE := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq E K U]
    rfl
  have hcomp : fieldSpecMap F A.inertia ≫ algebraBaseMap K A.field =
      algebraBaseMap K U := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    exact congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom A.factorization)
  refine ⟨{ field := A.field
            finite := A.finite
            galois := A.galois
            contains := hcontains
            inertia := A.inertia
            unramified := A.unramified
            iso := pullIso (algebraBaseMap K A.field) hq hq D.iso
            recovery := ?_ }⟩
  rw [pullIso_comp_base (algebraBaseMap E K) (algebraBaseMap K A.field)
    (fieldSpecMap F A.inertia) (fieldSpecMap F hcontains)
    (fieldSpecMap F hE) (algebraBaseMap K U) hq hp hk hcomp]
  exact finiteStage_recovery E U D hk

/-- Choose an actual finite unramified Galois stage for a specified isomorphism. -/
def isoStage
    {G H : GroupScheme (Spec (CommRingCat.of E))}
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (e : (baseChange (fieldSpecMap F hE)).obj G ≅
      (baseChange (fieldSpecMap F hE)).obj H) : IsoStage F E hE e :=
  Classical.choice (nonempty_isoStage F E hE e)

end Langlands.GroupScheme.Descent.FiniteUnramified
