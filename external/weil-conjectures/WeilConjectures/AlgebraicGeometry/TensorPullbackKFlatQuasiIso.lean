/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.InverseImageExactKFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Tensor pullback of quasi-isomorphisms between K-flat complexes

Source: Stacks Project, Cohomology, Tags 06YJ and 06YC.
(blueprint: lem-pc-tensor-pullback-kflat-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Tensor pullback preserves quasi-isomorphisms between K-flat complexes.
Source: Stacks Project, Cohomology, Tags 06YJ and 06YC; Cohomology on Sites, Tag 06YT.

Proof: exact inverse image preserves the quasi-isomorphism and takes the two K-flat
complexes to K-flat complexes over g⁻¹ O_S. For the second complex, apply resolution
preservation to its identity morphism. Apply the quasi-isomorphism preservation clause
of derived change of rings to g⁻¹ O_S → O_T. One may choose standard derived categories
locally for this application; the conclusion is about complexes and does not retain
these choices. The object and map formulas for change of rings identify the composite
with the recorded tensor pullback, so its termwise map is a quasi-isomorphism.
For completeness the change-of-rings clause follows by resolving O_T by a K-flat
complex: tensoring that resolution with each source K-flat complex preserves the
augmentation quasi-isomorphism, while tensoring the inverse-image quasi-isomorphism
with the resolution preserves it by K-flatness. The commutative square and two-out-of-
three give the claim. The argument works for arbitrary g, including the empty scheme
and the identity, without any flatness of its structure-sheaf map. Additivity only
provides the termwise complex functor.
(blueprint: lem-pc-tensor-pullback-kflat-quasi-iso). -/
theorem tensorPullback_quasiIso_of_isKFlat {T S : Scheme.{u}} (g : T ⟶ S)
    [(Scheme.Modules.tensorPullback g).Additive]
    {P Q : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ}
    (s : P ⟶ Q) (hP : CochainComplex.IsKFlatTensor (R := S.sheaf) P)
    (hQ : CochainComplex.IsKFlatTensor (R := S.sheaf) Q) (hs : QuasiIso s) :
    QuasiIso (((Scheme.Modules.tensorPullback g).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) := by
  obtain ⟨I, hI, hImap, hIa, _, _, hIr⟩ := exists_inverseImage_exact_kFlat g
  have := hIa
  have hIP := hIr s ⟨hs, hP⟩
  have hIQ := hIr (𝟙 Q) ⟨inferInstance, hQ⟩
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing g.base S.sheaf)))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings T.toRingedSpace))
  obtain ⟨E, hE, hEmap, hEa, hEq, _⟩ :=
    SheafOfModules.derivedChangeOfRings (Scheme.Modules.tensorPullbackRingMap g)
  have := hEa
  have hq := hEq ((I.mapHomologicalComplex (ComplexShape.up ℤ)).map s)
    hIP.2 hIQ.2 hIP.1
  have hobj (M) : (I ⋙ E).obj M = (Scheme.Modules.tensorPullback g).obj M := by
    exact (hE (I.obj M)).trans (congrArg _ (hI M))
  let e : I ⋙ E ≅ Scheme.Modules.tensorPullback g :=
    NatIso.ofComponents (fun M ↦ eqToIso (hobj M)) (by
      intro M N a
      dsimp
      rw [hEmap]
      simp only [Category.assoc, eqToHom_trans]
      rw [hImap]
      have transport
          {X X' Y Y' : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology T)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing g.base S.sheaf))}
          (p : X = X') (q : Y = Y') (b : X' ⟶ Y') :
          SheafOfModules.changeOfRingsHom.{u, u, u} (Scheme.Modules.tensorPullbackRingMap g) X
              (eqToHom p ≫ b ≫ eqToHom q.symm) =
            eqToHom (congrArg (SheafOfModules.changeOfRings.{u, u, u}
              (Scheme.Modules.tensorPullbackRingMap g)) p) ≫
              SheafOfModules.changeOfRingsHom.{u, u, u}
                (Scheme.Modules.tensorPullbackRingMap g) X' b ≫
                eqToHom (congrArg (SheafOfModules.changeOfRings.{u, u, u}
                  (Scheme.Modules.tensorPullbackRingMap g)) q.symm) := by
        subst X'
        subst Y'
        simp
      rw [transport (hI M) (hI N)]
      simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
      rfl)
  let ec := Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (ec.app P) (ec.app Q) (ec.hom.naturality s).symm)).mp hq

end AlgebraicGeometry
