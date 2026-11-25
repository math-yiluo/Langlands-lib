/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleLineFlatBraiding

/-! # Self symmetry of an even shifted etale line

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CoordinateTrace

variable (A : Type (u + 1)) [CommRing A]

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
/-- An even shifted rank-one line has identity self symmetry.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, second triangle,
last paragraph on even shifts; Stacks Tag 06YU.
(auxiliary; not a blueprint node).

Proof: trivialize the sheaf line on an etale cover. The existing etale evaluation
inverse makes the line flat. Braiding naturality identifies its ordinary
self-braiding with that of the tensor unit on each slice. Ordinary sheaf pullbacks
are jointly faithful, so this self-braiding is identity globally. For a single
complex in an even degree n, the only nonzero tensor summand has bidegree (n,n).
The explicit Koszul formula there is the ordinary self-braiding multiplied by
(-1)^(n*n), which is one. The single complex is K-flat; compatibility of the
canonical derived braiding with the invertible localization tensor comparison
therefore gives identity self-braiding for its derived image. Finally, the canonical
single/shift isomorphism identifies J[2d] with the derived single in degree -2d,
and braiding naturality transports the result to shiftedLine. This uses local
faithfulness only for ordinary sheaf maps, never for arbitrary derived morphisms. -/
theorem evenLineSelfSymmetry {Y : Scheme.{u}}
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (d : ℤ) :
    (swap A Y (shiftedLine A J d) (shiftedLine A J d)).hom = 𝟙 _ := by
  obtain ⟨hflat, hswap⟩ := etaleLineFlatAndBraiding A J hJ
  dsimp only [swap, Iso.app_hom, derivedTensorSymmetry, shiftedLine, tensor, derivedTensor]
  exact evenShiftCanonicalSelfSymmetry J hflat hswap d

end AlgebraicGeometry.Etale.CoordinateTrace
