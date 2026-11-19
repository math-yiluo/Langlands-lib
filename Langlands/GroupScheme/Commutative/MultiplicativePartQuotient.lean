import Langlands.GroupScheme.Commutative.MultiplicativePartCharacterizationStatement
import Langlands.GroupScheme.AffineNormalSubgroupQuotientProof
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Absolute.SolvableUnipotentKernelAssembly
import Langlands.GroupScheme.Torus.MultiplicativeTypeUnipotentHom
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeFieldComparison
import Langlands.GroupScheme.Unipotent.BaseChange

/-! # The multiplicative part of a commutative algebraic group: quotient and base-change steps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MultiplicativePart

variable {k : Type u} [Field k]

/-- Every subgroup functor of the points of a commutative group scheme is normal. -/
theorem isNormal_of_isCommMonObj {S : Scheme.{u}} {G : GroupScheme S} [IsCommMonObj G.X]
    (F : SubgroupFunctor G) : F.IsNormal := by
  intro T g x _ hx
  rw [mul_comm g x, mul_inv_cancel_right]
  exact hx

/-- An affine group scheme locally of finite type over a field has a Noetherian underlying
space. -/
theorem noetherianSpace (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] :
    TopologicalSpace.NoetherianSpace G.X.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsNoetherian G.X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian G.X.hom }
  infer_instance

/-- The target of a specified fppf quotient of a commutative affine group of finite type over a
field, by a closed subgroup, is affine and locally of finite type: it is isomorphic to the affine
quotient of Milne 5.14. -/
theorem quotient_affine_finiteType {G H Q : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X]
    (h : H ⟶ G) (hh : IsClosedSubgroup h) {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q) :
    IsAffineHom Q.X.hom ∧ LocallyOfFiniteType Q.X.hom := by
  obtain ⟨Q₀, q₀, hlft, haff, hq₀⟩ :=
    affineNormalSubgroupQuotient k G H h hh (isNormal_of_isCommMonObj _)
  have := noetherianSpace G
  let e := FppfQuotientComparison.iso hq hq₀
  let e' : Q.X.left ≅ Q₀.X.left := (Over.forget _).mapIso ((Grp.forget _).mapIso e)
  have hw : Q.X.hom = e'.hom ≫ Q₀.X.hom := (Over.w e.hom.hom.hom).symm
  have := haff
  have := hlft
  rw [hw]
  exact ⟨inferInstance, inferInstance⟩

/-- A group of multiplicative type over a field is of multiplicative type in the relative
(fppf-local) sense: it becomes diagonalizable over a finite Galois extension. -/
theorem isRelativeMultiplicativeType {H : GroupScheme (Spec (CommRingCat.of k))}
    (hH : IsMultiplicativeType H) : RelativeMultiplicativeType.IsMultiplicativeType H := by
  obtain ⟨K, hK, aK, hfin, hgal, Λ, hΛ, hfg, ⟨e⟩⟩ :=
    multiplicativeTypeFiniteGaloisSplitting k H hH
  let := hK
  let := aK
  let := hfin
  let := hgal
  let : Algebra.FinitePresentation k K :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hb : Etale b := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr
      ⟨Algebra.FormallyEtale.of_isSeparable k K, inferInstance⟩
  have hs : Surjective b := (fieldExtension_fpqc k K).1
  have : Etale b := hb
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
      (Spec (CommRingCat.of k)) :=
    Scheme.Cover.mkOfCovers PUnit (fun _ => Spec (CommRingCat.of K)) (fun _ => b)
      (fun x => by
        obtain ⟨y, hy⟩ := hs.surj x
        exact ⟨PUnit.unit, y, hy⟩) (fun _ => ⟨inferInstance, inferInstance⟩)
  refine ⟨𝒰, fun a => ?_⟩
  change RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange b).obj H)
  exact ⟨Λ, hΛ, hfg, ⟨e ≪≫ (Diagonalizable.baseChangeIso (Gm.toSpecZ _) Λ).symm⟩⟩

/-- Groups of multiplicative type over a field remain of multiplicative type after every field
extension. -/
theorem isMultiplicativeType_baseChange {H : GroupScheme (Spec (CommRingCat.of k))}
    (hH : IsMultiplicativeType H) (K : Type u) [Field K] [Algebra k K] :
    IsMultiplicativeType ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) :=
  (isRelativeMultiplicativeType hH).field_baseChange _

/-- Milne 14.18 applied to a specified fppf quotient: a closed subgroup of multiplicative type is
contained in the kernel of every fppf quotient map onto an affine unipotent group. -/
theorem range_le_of_isUnipotent_quotient {G H N Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom Q.X.hom] (h : H ⟶ G) (hH : IsMultiplicativeType H) (n : N ⟶ G) (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q) (hQ : IsUnipotent Q) :
    SubgroupFunctor.range h ≤ SubgroupFunctor.range n := by
  rw [← hq.2.2.2]
  exact range_le_kernelι_of_comp_eq_zero h q (hH.hom_eq_zero_of_isUnipotent hQ (h ≫ q))

end MultiplicativePart

end Langlands.GroupScheme
