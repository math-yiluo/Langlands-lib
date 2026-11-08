import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.RootSubgroupGaloisTransport
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Actual semilinear transport of normalized simple-root maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option autoImplicit false

namespace VectorGroup

variable {K : Type u} [Field K]
    (a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)) (d : ℕ)

/-- The actual pulled-back vector group has the same global coordinates on
the test scheme with its structure changed by the base endomorphism. -/
def baseEndomorphismCoordinates (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ ((GroupScheme.baseChange a).obj (groupScheme (CommRingCat.of K) d)).X) ≃*
      Multiplicative (Fin d → Γ(T.left, ⊤)) :=
  (baseChangePointsEquiv a (groupScheme (CommRingCat.of K) d) T).trans
    (coordinates (CommRingCat.of K) d ((Over.map a).obj T))

theorem baseEndomorphismCoordinates_natural :
    RelativeRoot.IsNaturalVectorCoordinates (baseEndomorphismCoordinates a d) := by
  intro T W f v
  simp only [baseEndomorphismCoordinates, MulEquiv.trans_apply,
    baseChangePointsEquiv_naturality]
  exact isNaturalVectorCoordinates ((Over.map a).obj T) ((Over.map a).obj W)
    ((Over.map a).map f)
    (baseChangePointsEquiv a (groupScheme (CommRingCat.of K) d) T v)

/-- Identify the pulled-back standard vector group with the standard group
by retaining the same global coordinates. -/
def baseEndomorphismIso :
    (GroupScheme.baseChange a).obj (groupScheme (CommRingCat.of K) d) ≅
      groupScheme (CommRingCat.of K) d :=
  RelativeRoot.vectorGroupIso (baseEndomorphismCoordinates a d)
    (baseEndomorphismCoordinates_natural a d)

theorem coordinates_baseEndomorphismIso_hom
    (T : Over (Spec (CommRingCat.of K)))
    (v : T ⟶ ((GroupScheme.baseChange a).obj (groupScheme (CommRingCat.of K) d)).X) :
    coordinates (CommRingCat.of K) d T
        (v ≫ (baseEndomorphismIso a d).hom.hom.hom) =
      baseEndomorphismCoordinates a d T v :=
  RelativeRoot.coordinates_comp_vectorGroupIso_hom _ _ T v

/-- The inverse comparison preserves each scalar parameter. -/
theorem baseChangePointsEquiv_scalarPoint_baseEndomorphismIso_inv
    (T : Over (Spec (CommRingCat.of K))) (c : Γ(T.left, ⊤)) :
    baseChangePointsEquiv a (groupScheme (CommRingCat.of K) 1) T
        (scalarPoint (CommRingCat.of K) T c ≫
          (baseEndomorphismIso a 1).inv.hom.hom) =
      scalarPoint (CommRingCat.of K) ((Over.map a).obj T) c := by
  apply (coordinates (CommRingCat.of K) 1 _).injective
  have h := coordinates_baseEndomorphismIso_hom a 1 T
    (scalarPoint (CommRingCat.of K) T c ≫ (baseEndomorphismIso a 1).inv.hom.hom)
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id] at h
  exact h.symm.trans (by
    apply Multiplicative.toAdd.injective
    funext j
    exact (coordinates_scalarPoint (CommRingCat.of K) T c j).trans
      (coordinates_scalarPoint (CommRingCat.of K) ((Over.map a).obj T) c j).symm)

end VectorGroup

section DescentPoints

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
    (G : GroupScheme B)

/-- Descending a point after the canonical ambient identification recovers
the ordinary base-change point comparison. -/
theorem descentPoint_comp_descentBaseChangeIso
    (T : Over S)
    (y : T ⟶ ((GroupScheme.baseChange a).obj ((GroupScheme.baseChange b).obj G)).X) :
    descentPoint b a ha G T (y ≫ (descentBaseChangeIso b a ha G).hom.hom.hom) =
      baseChangePointsEquiv a ((GroupScheme.baseChange b).obj G) T y := by
  apply (baseChangePointsEquiv b G ((Over.map a).obj T)).injective
  rw [baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_descent]
  exact Iso.inv_hom_id_assoc _ _

/-- Descent commutes with an actually pulled-back homomorphism. -/
theorem descentPoint_comp_baseChangeHom {H : GroupScheme S}
    (f : H ⟶ (GroupScheme.baseChange b).obj G) (T : Over S)
    (y : T ⟶ ((GroupScheme.baseChange a).obj H).X) :
    descentPoint b a ha G T
        (y ≫ ((GroupScheme.baseChange a).map f ≫
          (descentBaseChangeIso b a ha G).hom).hom.hom) =
      baseChangePointsEquiv a H T y ≫ f.hom.hom := by
  rw [Grp.comp_hom_hom, ← Category.assoc,
    descentPoint_comp_descentBaseChangeIso, baseChangePointsEquiv_comp]

/-- Actual transport of a homomorphism with a supplied source comparison. -/
def semilinearDescentHom {H V : GroupScheme S}
    (e : V ≅ (GroupScheme.baseChange a).obj H)
    (f : H ⟶ (GroupScheme.baseChange b).obj G) : V ⟶ (GroupScheme.baseChange b).obj G :=
  e.hom ≫ ((GroupScheme.baseChange a).map f ≫
    (descentBaseChangeIso b a ha G).hom)

/-- The same point formula after an arbitrary source comparison. -/
theorem semilinearDescentHom_point {H V : GroupScheme S}
    (e : V ≅ (GroupScheme.baseChange a).obj H)
    (f : H ⟶ (GroupScheme.baseChange b).obj G) (T : Over S)
    (y : T ⟶ V.X) :
    descentPoint b a ha G T
        (y ≫ (semilinearDescentHom b a ha G e f).hom.hom) =
      baseChangePointsEquiv a H T (y ≫ e.hom.hom.hom) ≫ f.hom.hom := by
  rw [semilinearDescentHom, Grp.comp_hom_hom, ← Category.assoc, descentPoint_comp_baseChangeHom]

end DescentPoints

namespace VectorGroup

variable {B : Scheme.{u}} {K : Type u} [Field K]
    (b : Spec (CommRingCat.of K) ⟶ B)
    (a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (ha : a ≫ b = b) (G : GroupScheme B)

/-- The standard-source transport evaluates at the original global scalar. -/
theorem semilinearDescentHom_scalarPoint
    (f : groupScheme (CommRingCat.of K) 1 ⟶ (GroupScheme.baseChange b).obj G)
    (T : Over (Spec (CommRingCat.of K))) (c : Γ(T.left, ⊤)) :
    descentPoint b a ha G T
        (scalarPoint (CommRingCat.of K) T c ≫
          (semilinearDescentHom b a ha G (baseEndomorphismIso a 1).symm f).hom.hom) =
      scalarPoint (CommRingCat.of K) ((Over.map a).obj T) c ≫ f.hom.hom :=
  (semilinearDescentHom_point b a ha G (baseEndomorphismIso a 1).symm f T
    (scalarPoint (CommRingCat.of K) T c)).trans
      (congrArg (fun y => y ≫ f.hom.hom)
        (baseChangePointsEquiv_scalarPoint_baseEndomorphismIso_inv a T c))

end VectorGroup

namespace SplitPinning.NormalizedRootParametrization

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance steinbergSemilinearBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable {p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)}
    {a : p.base.support} (x : p.NormalizedRootParametrization a) (σ : K ≃ₐ[k] K)

/-- Pull back the entire root homomorphism along the coefficient spectrum
automorphism, keeping standard source coordinates and the original ambient group. -/
def galoisHom :
    VectorGroup.groupScheme (CommRingCat.of K) 1 ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G :=
  semilinearDescentHom (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) G
    (VectorGroup.baseEndomorphismIso (galoisBaseMap k K σ) 1).symm x.hom

theorem galoisHom_eq_semilinearDescentHom :
    x.galoisHom k K G σ =
      semilinearDescentHom (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G
        (VectorGroup.baseEndomorphismIso (galoisBaseMap k K σ) 1).symm x.hom := rfl

/-- On every scheme test, canonical descent evaluates the original root map
with the same global scalar on the changed-structure test. -/
theorem galoisHom_point (T : Over (Spec (CommRingCat.of K))) (c : Γ(T.left, ⊤)) :
    descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G T
        (VectorGroup.scalarPoint (CommRingCat.of K) T c ≫
          (x.galoisHom k K G σ).hom.hom) =
      x.point ((Over.map (galoisBaseMap k K σ)).obj T) c := by
  rw [galoisHom_eq_semilinearDescentHom]
  exact VectorGroup.semilinearDescentHom_scalarPoint (algebraBaseMap k K)
    (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) G x.hom T c

/-- The transported whole homomorphism represents the transported all-test
root subgroup, before any compatibility of simple-root choices is imposed. -/
theorem galoisHom_range :
    SubgroupFunctor.range (x.galoisHom k K G σ) =
      SubgroupFunctor.galoisTransport k K G σ
        (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)) := by
  have h := SubgroupFunctor.range_iso_comp
    (VectorGroup.baseEndomorphismIso (galoisBaseMap k K σ) 1).symm
    ((GroupScheme.baseChange (galoisBaseMap k K σ)).map x.hom ≫
      (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G).hom)
  exact h.trans ((SubgroupFunctor.descentTransport_range (algebraBaseMap k K)
    (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) G x.hom).symm.trans
      (congrArg (SubgroupFunctor.galoisTransport k K G σ) x.represents.2))

/-- Closedness is preserved by actual pullback and the two comparison isomorphisms. -/
theorem galoisHom_isClosedSubgroup :
    IsClosedSubgroup (x.galoisHom k K G σ) := by
  have hc := x.isClosedSubgroup.baseChange (galoisBaseMap k K σ)
  change IsClosedImmersion
    ((VectorGroup.baseEndomorphismIso (galoisBaseMap k K σ) 1).inv.hom.hom.left ≫
      (((GroupScheme.baseChange (galoisBaseMap k K σ)).map x.hom).hom.hom.left ≫
        (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G).hom.hom.hom.left))
  have : IsClosedImmersion
      ((GroupScheme.baseChange (galoisBaseMap k K σ)).map x.hom).hom.hom.left := hc
  infer_instance

theorem galoisHom_represents :
    (SubgroupFunctor.galoisTransport k K G σ
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a))).IsRepresentedBy
        (x.galoisHom k K G σ) := by
  refine ⟨?_, x.galoisHom_range k K G σ⟩
  exact (x.galoisHom_isClosedSubgroup k K G σ).mono_overHom

end SplitPinning.NormalizedRootParametrization

end Langlands.GroupScheme
