import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.Descent.QuasiSplitDatum
import Langlands.GroupScheme.Absolute.ParabolicGeometricWitnessTransport
import Langlands.GroupScheme.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Rational.CentralMaximalSplitParabolic

/-! # Effective descent of Galois-invariant actual parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section Reflection

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Algebra.IsAlgebraic F L]
  {P G : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G}

/-- Parabolicity of the original closed inclusion is reflected by an algebraic
field extension. Its geometric Borel witness is transported through the actual
isomorphism of the two chosen algebraic closures. -/
theorem IsParabolicSubgroup.of_baseChange_of_algebraicExtension
    (hp : IsParabolicSubgroup
      ((GroupScheme.baseChange (algebraBaseMap F L)).map p))
    (hclosed : IsClosedSubgroup p) : IsParabolicSubgroup p := by
  let b := algebraBaseMap F L
  let a := toAlgebraicClosure F
  let d := algebraicClosureBaseMap F L
  let : Algebra (AlgebraicClosure F) (AlgebraicClosure L) :=
    (algebraicClosureEmbedding F L).toRingHom.toAlgebra
  have : IsScalarTower F (AlgebraicClosure F) (AlgebraicClosure L) :=
    IsScalarTower.of_algebraMap_eq fun x => ((algebraicClosureEmbedding F L).commutes x).symm
  have : Algebra.IsAlgebraic (AlgebraicClosure F) (AlgebraicClosure L) :=
    Algebra.IsAlgebraic.tower_top (K := F) (AlgebraicClosure F)
  have : IsIso d := isIso_SpecMap_iff.mpr
    (IsAlgClosed.algebraMap_bijective_of_isIntegral :
      Function.Bijective (algebraMap (AlgebraicClosure F) (AlgebraicClosure L)))
  have : Surjective b := (fieldExtension_fpqc F L).1
  have : Flat b := (fieldExtension_fpqc F L).2.1
  have : QuasiCompact b := (fieldExtension_fpqc F L).2.2
  refine ⟨hclosed, smooth_of_baseChange b P hp.smooth, ?_⟩
  let E := algebraicClosureBaseChangeIso F L
  obtain ⟨B, j, f, hj, hf⟩ := hp.exists_isBorelSubgroup
  change f ≫ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap F L))) ⋙
    GroupScheme.baseChange (toAlgebraicClosure L)).map p = j at hf
  let jD := j ≫ (E.app G).inv
  let fD := f ≫ (E.app P).inv
  have hjD : IsBorelSubgroup jD := hj.comp_iso (E.app G).symm
  have hfD : fD ≫ (GroupScheme.baseChange d).map
      ((GroupScheme.baseChange a).map p) = jD := by
    change (f ≫ E.inv.app P) ≫
      (GroupScheme.baseChange a ⋙ GroupScheme.baseChange d).map p =
        j ≫ E.inv.app G
    rw [Category.assoc, ← E.inv.naturality p, ← Category.assoc, hf]
  let R := GroupScheme.baseChange (inv d)
  let e := baseChangeSectionNatIso d (inv d) (IsIso.inv_hom_id d)
  refine ⟨R.obj B, R.map jD ≫ (e.app ((GroupScheme.baseChange a).obj G)).hom,
    R.map fD ≫ (e.app ((GroupScheme.baseChange a).obj P)).hom,
    (hjD.baseChange_of_isIso (inv d)).comp_iso
      (e.app ((GroupScheme.baseChange a).obj G)), ?_⟩
  have hn := e.hom.naturality ((GroupScheme.baseChange a).map p)
  change R.map ((GroupScheme.baseChange d).map ((GroupScheme.baseChange a).map p)) ≫
      (e.app ((GroupScheme.baseChange a).obj G)).hom =
    (e.app ((GroupScheme.baseChange a).obj P)).hom ≫
      (GroupScheme.baseChange a).map p at hn
  change (R.map fD ≫ (e.app ((GroupScheme.baseChange a).obj P)).hom) ≫
      (GroupScheme.baseChange a).map p =
    R.map jD ≫ (e.app ((GroupScheme.baseChange a).obj G)).hom
  rw [Category.assoc, ← hn, ← Category.assoc, ← R.map_comp, hfD]

end Reflection

namespace Descent

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {P : GroupScheme (Spec (CommRingCat.of L))}
  (p : P ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)

/-- An actual ground-field parabolic with an exact recovery of the supplied
upper-field inclusion. -/
structure ParabolicGaloisDescentData where
  obj : GroupScheme (Spec (CommRingCat.of F))
  inclusion : obj ⟶ G
  affine : IsAffine obj.X.left
  parabolic : IsParabolicSubgroup inclusion
  recoveryIso : (GroupScheme.baseChange (algebraBaseMap F L)).obj obj ≅ P
  recovery : (GroupScheme.baseChange (algebraBaseMap F L)).map inclusion =
    recoveryIso.hom ≫ p

variable {p} [IsAffineHom G.X.hom] [IsGalois F L]

/-- The proved closed-subgroup descent and algebraic-extension reflection of
parabolicity construct a descent of any all-test Galois-invariant parabolic. -/
theorem nonempty_parabolicGaloisDescentData
    (hp : IsParabolicSubgroup p)
    (hinv : ∀ σ : L ≃ₐ[F] L,
      SubgroupFunctor.range (radicalGaloisHom p σ) = SubgroupFunctor.range p) :
    Nonempty (ParabolicGaloisDescentData p) := by
  obtain ⟨P₀, j, e, hP₀, hj, he⟩ :=
    GaloisInvariantClosedSubgroup.exists_descent hp.isClosedSubgroup hinv
  have hpar : IsParabolicSubgroup
      ((GroupScheme.baseChange (algebraBaseMap F L)).map j) := by
    rw [he]
    exact hp.iso_comp e
  exact ⟨⟨P₀, j, hP₀, hpar.of_baseChange_of_algebraicExtension hj, e, he⟩⟩

/-- A selected effective descent retains the original upper-field parabolic
and the exact comparison of its inclusion with the base-changed ground-field map. -/
def parabolicGaloisDescent
    (hp : IsParabolicSubgroup p)
    (hinv : ∀ σ : L ≃ₐ[F] L,
      SubgroupFunctor.range (radicalGaloisHom p σ) = SubgroupFunctor.range p) :
    ParabolicGaloisDescentData p :=
  Classical.choice (nonempty_parabolicGaloisDescentData hp hinv)

end Descent

section CentralMaximalSplit

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [IsGalois F L]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {s : S.toGrp ⟶ G}
  {P : GroupScheme (Spec (CommRingCat.of L))}
  {p : P ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G}

/-- A central maximal split torus excludes every proper Galois-invariant actual
parabolic in an algebraic Galois extension: effective descent produces a rational
parabolic, whose original inclusion is an isomorphism. -/
theorem IsMaximalSplitTorus.isIso_parabolic_of_galoisInvariant
    (hs : IsMaximalSplitTorus s) (hc : IsCentral s) (hG : IsConnectedReductive G)
    (hp : IsParabolicSubgroup p)
    (hinv : ∀ σ : L ≃ₐ[F] L,
      SubgroupFunctor.range (radicalGaloisHom p σ) = SubgroupFunctor.range p) :
    IsIso p := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let D := Descent.parabolicGaloisDescent hp hinv
  have : IsIso D.inclusion := hs.isIso_parabolic_of_isCentral hc hG D.parabolic
  have he : D.recoveryIso.inv ≫
      (GroupScheme.baseChange (algebraBaseMap F L)).map D.inclusion = p := by
    rw [D.recovery, Iso.inv_hom_id_assoc]
  rw [← he]
  infer_instance

end CentralMaximalSplit

end Langlands.GroupScheme
