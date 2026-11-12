/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U010.Definitions
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Targets for cardinal image–kernel index laws

Modified by Worker 120: extract M006.023–025 signatures from the pinned
NYLL Degree/Indices.lean, prefix the namespace with Langlands.NYLL,
and replace each theorem by its Prop-valued Statement target.
Preserve independent source universes, lifts, binder order and hypotheses.
Reuse the published cardinal-index definitions and Mathlib subgroup kernels.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

universe u v

variable {G : Type u} {D : Type v} [Group G] [Group D]

/-- Target for the image contribution as the saturated intersection index. -/
def intersectionIndexCardinal_image_eq_saturationStatement (d : G →* D)
    (L K : Subgroup G) : Prop :=
  Cardinal.lift.{u} (intersectionIndexCardinal (L.map d) (K.map d)) =
    Cardinal.lift.{v}
      (intersectionIndexCardinal (K ⊓ (L ⊔ d.ker)) K)

/-- Target for the kernel contribution as the saturated inner index. -/
def relativeIndexCardinal_kernel_eq_saturationStatement (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) : Prop :=
  relativeIndexCardinal
    (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl) =
    relativeIndexCardinal
      (show L ≤ K ⊓ (L ⊔ d.ker) from fun _ hx ↦
        ⟨hLK hx, (show L ≤ L ⊔ d.ker from le_sup_left) hx⟩)

/-- Target for the cardinal image–kernel factorization of an inclusion index. -/
def relativeIndexCardinal_eq_map_mul_inf_kerStatement (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) : Prop :=
  Cardinal.lift.{v} (relativeIndexCardinal hLK) =
    Cardinal.lift.{u}
        (relativeIndexCardinal (Subgroup.map_mono (f := d) hLK)) *
      Cardinal.lift.{v}
        (relativeIndexCardinal
          (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl))

end Langlands.NYLL.ClassFormation
