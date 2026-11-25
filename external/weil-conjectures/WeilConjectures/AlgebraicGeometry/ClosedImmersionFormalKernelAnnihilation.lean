/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.ClosedImmersionFormalKernelComparison
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealPowerAnnihilation
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Annihilation of a transported formal kernel

Source: Stacks Project, Cohomology of Schemes, Theorem 088E and Tags 087T, 087W, 087X.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A commuting pushforward square transports annihilation of a formal kernel by
an ideal power to annihilation by the inverse image ideal.

Source: Stacks Project, Theorem 088E, paragraphs 2--4, and Tags 087T, 087W, 087X.
(blueprint: lem-weil-pbc-closed-immersion-formal-kernel-annihilation).

Proof: Closed pushforward identifies formal systems on Z with the full subcategory
of systems on X annihilated by j.ker. This subcategory is closed under categorical
kernels: on each Noetherian affine, identify formal systems with finite modules over
the adic completion. On Spec A with Z = Spec(A/I), termwise pushforward is
restriction of scalars. The inverse limits used by the affine equivalence have the
same elements and maps before and after restriction of scalars; hence their kernels
are the same sets with the restricted action. Restriction of scalars preserves these
kernels. The kernel is finite by Noetherianity and is killed by I. Reduction of this
finite kernel modulo the adic powers identifies its formal terms, so pushforward
preserves the categorical formal kernel. These identifications commute with
restriction; exactness is local by Tag 087X, so the statement holds
globally and for any chosen Abelian structure. The equivalence therefore takes the
limiting fork k to a limiting kernel fork. The commuting square and its two
isomorphisms identify its point with kernel a by the kernel universal property.
On an affine open, the ideal (L^t).map j is the inverse image of L^t under the
surjective structure ring map. Multiplication on a pushed module factors through
this quotient ring, so the assumed L^t-annihilation kills each pushed term of k.pt.
Transport this vanishing through the kernel isomorphism, term by term. This uses
categorical formal kernels, not a claim that evaluation preserves kernels. -/
theorem closedImmersion_formalKernel_annihilated
    {X Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z]
    (j : Z ⟶ X) [IsClosedImmersion j] (Q : X.IdealSheafData)
    [Abelian (CoherentFormalModule X Q)]
    (M N : CoherentFormalModule X Q)
    (G D : CoherentFormalModule Z (Q.comap j))
    (a : M ⟶ N) (α : G ⟶ D)
    (e : M.obj ≅ G.obj ⋙ Scheme.Modules.pushforward j)
    (d : N.obj ≅ D.obj ⋙ Scheme.Modules.pushforward j)
    (hsquare : a.hom ≫ d.hom =
      e.hom ≫ Functor.whiskerRight α.hom (Scheme.Modules.pushforward j))
    (L : Z.IdealSheafData) (t : ℕ) (k : KernelFork α) (hk : IsLimit k)
    (hkill : ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower L.toModulesι t).2 (k.pt.obj.obj (op n)))) :
    AnnihilatedBy Q ((L ^ t).map j) (kernel a) := by
  obtain ⟨q⟩ := closedImmersion_formalKernel_comparison j Q M N G D a α e d hsquare k hk
  intro n
  have hF := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Z
    (k.pt.obj.obj (op n))).mp (k.pt.property.1 n)
  have hH := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X
    ((kernel a).obj.obj (op n))).mp ((kernel a).property.1 n)
  let := hF.1
  let := hH.1
  exact Scheme.closedImmersion_idealPower_annihilation j L t (k.pt.obj.obj (op n))
    ((kernel a).obj.obj (op n)) (q.app (op n)) (hkill n)

end AlgebraicGeometry
