import Langlands.GroupScheme.Reductive.StarAction

/-! # Ordinary Galois action on actual coroots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 350000

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (p : GaloisPinningData F E G)

local notation "b" => algebraBaseMap F E
local notation "BG" => GroupScheme.baseChange b
local notation "BC" => CommGroupScheme.baseChange b
local notation "GE" => Functor.obj BG G
local notation "TE" => Functor.obj BC p.torus
local notation "tE" => CategoryTheory.Functor.map BG p.inclusion

/-- Ordinary Galois action on root indices induces ordinary Galois action
on the corresponding actual coroots. -/
theorem GaloisPinningData.galoisAction_coroot
    (σ : E ≃ₐ[F] E) (a : p.rootIndex) :
    p.rootDatum.coroot ((p.galoisAction σ).indexEquiv a) =
      cocharacterLattice.galoisRepresentation F E p.torus σ (p.rootDatum.coroot a) := by
  let : IsAffineHom (GE).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : LocallyOfFiniteType (GE).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : Mono (tE).hom.hom.left := p.isMaximalTorus.2.1.mono
  let : Finite (weylImage (T := TE) tE) :=
    splitTorusWeylImageFinite E (GE) (TE) p.isSplitTorus tE p.isMaximalTorus.2.1
  exact IsRootDatumOf.galoisRootIndexEquiv_coroot F E p.inclusion p.isRootDatum σ a

end Langlands.GroupScheme
