import Langlands.GroupScheme.IntegralModel.KernelCentralizerTorus
import Langlands.GroupScheme.Rational.KernelCentralizerQuotientGeometry
import Langlands.GroupScheme.KernelSquareTransport

/-! # Quotients of the actual fibres of integral kernel centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.KernelCentralizerData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K G}
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {i : T.toGrp ⟶ M.group} {a : characterLattice T}
    (D : KernelCentralizerData M i a)
    {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    {H E : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth E.X.hom] [IsAffineHom E.X.hom]
    (q : (baseChange b).obj M.group ⟶ H)
    {jE : E ⟶ H}
    (hE : (RelativeRoot.kernelCentralizer ((baseChange b).map i ≫ q)
      (characterLattice.baseChange b T a)).IsRepresentedBy jE)

local instance : Smooth ((baseChange b).obj D.fullGroup).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd D.fullGroup.X.hom b))

local instance : IsAffineHom ((baseChange b).obj D.fullGroup).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd D.fullGroup.X.hom b))

/-- The quotient map on the actual fibre of the integral centralizer component,
using the canonical comparison with the ordinary full-centralizer component. -/
def fibreQuotientMap :
    (baseChange b).obj D.componentGroup ⟶ identityComponent E :=
  (D.fibreIso b).hom ≫
    RelativeRoot.kernelCentralizerIdentityMap
      (S := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map i) (characterLattice.baseChange b T a) q
      (D.fullFibreRepresents b) hE

/-- The actual fibre quotient commutes with both original ambient inclusions. -/
@[reassoc]
theorem fibreQuotientMap_comp_ambient :
    D.fibreQuotientMap b q hE ≫ (identityComponentι E ≫ jE) =
      (baseChange b).map (D.componentHom ≫ D.fullHom) ≫ q := by
  rw [fibreQuotientMap, Category.assoc,
    RelativeRoot.kernelCentralizerIdentityMap_comp_ambient]
  rw [← Category.assoc, ← Category.assoc, fibreIso_hom_comp]
  simp only [Functor.map_comp, Category.assoc]

/-- The quotient uses the base change of the specified integral torus and the
unchanged base-changed character. -/
theorem fibreQuotientMap_torus (hT : IsSplitTorus T.toGrp) :
    (baseChange b).map (D.torus hT) ≫ D.fibreQuotientMap b q hE =
      RelativeRoot.kernelCentralizerIdentityTorus
        (T := (CommGroupScheme.baseChange b).obj T)
        ((baseChange b).map i ≫ q) (hT.baseChange b)
        (characterLattice.baseChange b T a) jE hE := by
  rw [fibreQuotientMap, ← Category.assoc, torus_fibreIso]
  exact RelativeRoot.kernelCentralizerIdentityMap_torus
    (S := (CommGroupScheme.baseChange b).obj T)
    (G := (baseChange b).obj M.group) (H := H)
    (C := (baseChange b).obj D.fullGroup) (E := E)
    ((baseChange b).map i) (characterLattice.baseChange b T a) q
    (D.fullFibreRepresents b) hE (hT.baseChange b)

/-- The ambient square detects the identity on every relative test scheme. -/
theorem fibreQuotientMap_eq_one_iff
    {X : Over (Spec (CommRingCat.of k))}
    (x : X ⟶ ((baseChange b).obj D.componentGroup).X) :
    x ≫ (D.fibreQuotientMap b q hE).hom.hom = 1 ↔
      x ≫ ((baseChange b).map (D.componentHom ≫ D.fullHom) ≫ q).hom.hom = 1 := by
  have : Mono jE.hom.hom := hE.1
  have : Mono (identityComponentι E ≫ jE).hom.hom := by
    change Mono ((identityComponentι E).hom.hom ≫ jE.hom.hom)
    infer_instance
  have hs :
      (x ≫ (D.fibreQuotientMap b q hE).hom.hom) ≫
          (identityComponentι E ≫ jE).hom.hom =
        x ≫ ((baseChange b).map (D.componentHom ≫ D.fullHom) ≫ q).hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, fibreQuotientMap_comp_ambient]
  constructor
  · intro hx
    rw [← hs, hx, MonObj.one_comp]
  · intro hx
    apply (cancel_mono (identityComponentι E ≫ jE).hom.hom).mp
    rw [hs, hx, MonObj.one_comp]

/-- Nonidentity in the original ambient quotient implies nonidentity in the
actual component quotient. -/
theorem fibreQuotientMap_ne_one_of_ambient
    {X : Over (Spec (CommRingCat.of k))}
    (x : X ⟶ ((baseChange b).obj D.componentGroup).X)
    (hx : x ≫ ((baseChange b).map (D.componentHom ≫ D.fullHom) ≫ q).hom.hom ≠ 1) :
    x ≫ (D.fibreQuotientMap b q hE).hom.hom ≠ 1 :=
  mt (D.fibreQuotientMap_eq_one_iff b q hE x).mp hx

section Geometry

variable [IsAffineHom H.X.hom]

local instance : IsAffineHom ((baseChange b).obj M.group).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd M.group.X.hom b))

/-- The full actual kernel of the fibre quotient retains the ambient smooth,
connected, unipotent kernel geometry over a perfect field. -/
theorem fibreQuotientMap_kernel_geometry [PerfectField k]
    (hT : IsSplitTorus T.toGrp) (hq : HasSmoothConnectedUnipotentKernel q) :
    HasSmoothConnectedUnipotentKernel (D.fibreQuotientMap b q hE) := by
  let p := RelativeRoot.kernelCentralizerIdentityMap
    (S := (CommGroupScheme.baseChange b).obj T)
    ((baseChange b).map i) (characterLattice.baseChange b T a) q
    (D.fullFibreRepresents b) hE
  have hp : HasSmoothConnectedUnipotentKernel p :=
    RelativeRoot.kernelCentralizerIdentityMap_kernel_geometry
      (S := (CommGroupScheme.baseChange b).obj T)
      (G := (baseChange b).obj M.group) (H := H)
      (C := (baseChange b).obj D.fullGroup) (E := E)
      ((baseChange b).map i) (characterLattice.baseChange b T a) q
      (hT.baseChange b) hq (D.fullFibreRepresents b) hE (D.fullClosed.baseChange b)
  exact smooth_connected_unipotent_of_groupIso
    (kernelSquareIso (D.fibreQuotientMap b q hE) p (D.fibreIso b)
      (Iso.refl _) (by rw [Iso.refl_hom, Category.comp_id]; rfl)) hp

variable [Smooth M.group.X.hom] [Smooth H.X.hom]

local instance : Smooth ((baseChange b).obj M.group).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd M.group.X.hom b))

/-- A smooth ambient quotient gives a smooth scheme-surjective quotient of
the actual integral component fibre. -/
theorem fibreQuotientMap_smooth_surjective
    (hT : IsSplitTorus T.toGrp) (hqs : Smooth q.hom.hom.left) :
    Smooth (D.fibreQuotientMap b q hE).hom.hom.left ∧
      Surjective (D.fibreQuotientMap b q hE).hom.hom.left := by
  let p := RelativeRoot.kernelCentralizerIdentityMap
    (S := (CommGroupScheme.baseChange b).obj T)
    ((baseChange b).map i) (characterLattice.baseChange b T a) q
    (D.fullFibreRepresents b) hE
  have hp := RelativeRoot.kernelCentralizerIdentityMap_smooth_surjective
    (S := (CommGroupScheme.baseChange b).obj T)
    (G := (baseChange b).obj M.group) (H := H)
    (C := (baseChange b).obj D.fullGroup) (E := E)
    ((baseChange b).map i) (characterLattice.baseChange b T a) q
    (hT.baseChange b) hqs (D.fullFibreRepresents b) hE
  have : Smooth p.hom.hom.left := hp.1
  have : Surjective p.hom.hom.left := hp.2
  have : IsIso (D.fibreIso b).hom.hom.hom :=
    (Grp.forget _).map_isIso (D.fibreIso b).hom
  have : IsIso (D.fibreIso b).hom.hom.hom.left :=
    (Over.forget _).map_isIso (D.fibreIso b).hom.hom.hom
  change Smooth ((D.fibreIso b).hom.hom.hom.left ≫ p.hom.hom.left) ∧
    Surjective ((D.fibreIso b).hom.hom.hom.left ≫ p.hom.hom.left)
  exact ⟨inferInstance, inferInstance⟩

/-- The actual component-fibre quotient, with smoothness, scheme
surjectivity and its full smooth connected unipotent kernel. -/
def fibreQuotient [PerfectField k] (hT : IsSplitTorus T.toGrp)
    (hq : HasSmoothConnectedUnipotentKernel q) (hqs : Smooth q.hom.hom.left) :
    {p : (baseChange b).obj D.componentGroup ⟶ identityComponent E //
      Smooth p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
        HasSmoothConnectedUnipotentKernel p} :=
  ⟨D.fibreQuotientMap b q hE,
    (D.fibreQuotientMap_smooth_surjective b q hE hT hqs).1,
    (D.fibreQuotientMap_smooth_surjective b q hE hT hqs).2,
    D.fibreQuotientMap_kernel_geometry b q hE hT hq⟩

end Geometry

end Langlands.GroupScheme.IntegralModel.KernelCentralizerData
