import Langlands.Algebra.NondegenerateTensorFunctor

/-!
# Complete interfaces and boundary checks for the actual tensor functors

Internal checks retaining independent universes and named original structures.
The same-stem Markdown explains their provenance and scope.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NondegenerateTensorFunctorChecks

open CategoryTheory MulOpposite
open Langlands.Algebra.NondegenerateTensorFunctor
open Langlands.Algebra.NonUnitalModuleTensor (Tensor tmul)

universe uS uR uX uA uB v w z

section Interfaces
set_option linter.unusedVariables false

/-! Arbitrary independent ring, first-factor and variable carrier universes. -/

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X),
    NonUnitalModuleCat.{uR, v} R ⥤ NonUnitalModuleCat.{uS, max uX v} S := @functor

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X),
    (functor.{uS, uR, uX, v} hX).Additive := @functor_additive

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X)
    (M : Type v) [AddCommGroup M] [NonUnitalModule R M],
    @IsNondegenerate S (Tensor R X M) _ (NonUnitalModuleTensor.addCommGroup R X M)
      (NonUnitalBimoduleTensor.leftModule hX M) := @isNondegenerate

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    NonUnitalModuleCat.{uR, v} R ⥤ NondegenerateModuleCat.{uS, max uX v} S := @nondegenerateFunctor

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    (nondegenerateFunctor.{uS, uR, uX, v} hS hX hnd).Additive := @nondegenerateFunctor_additive

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    nondegenerateFunctor.{uS, uR, uX, v} hS hX hnd ⋙ nondegenerateInclusion S =
      functor hX := @nondegenerateFunctor_comp_inclusion

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    NondegenerateModuleCat.{uR, v} R ⥤ NondegenerateModuleCat.{uS, max uX v} S := @restrictedFunctor

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    (restrictedFunctor.{uS, uR, uX, v} hS hX hnd).Additive := @restrictedFunctor_additive

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule R M] [NonUnitalModule R N],
    NonUnitalModuleHom R M N → NonUnitalModuleHom S (tensorObj hX M) (tensorObj hX N) := @map

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule R M] [NonUnitalModule R N],
    NonUnitalModuleHom R M N →+ NonUnitalModuleHom S (tensorObj hX M) (tensorObj hX N) := @mapAddHom

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule R M] [NonUnitalModule R N]
    (f : NonUnitalModuleHom R M N),
    (map hX f).toAddMonoidHom =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) f := @map_toAddMonoidHom

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type v} [AddCommGroup M] [NonUnitalModule R M],
    map hX (NonUnitalModuleHom.id R M) = NonUnitalModuleHom.id S (tensorObj hX M) := @map_id

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type v} {N : Type w} {P : Type z}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [NonUnitalModule R M] [NonUnitalModule R N] [NonUnitalModule R P]
    (g : NonUnitalModuleHom R N P) (f : NonUnitalModuleHom R M N),
    map hX (g.comp f) = (map hX g).comp (map hX f) := @map_comp

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X)
    {M N : NonUnitalModuleCat.{uR, v} R} (f : M ⟶ N),
    ((nondegenerateFunctor hS hX hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hX hX (NonUnitalBimoduleHom.id S R X) f := @nondegenerateFunctor_map_hom

example : ∀ {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X)
    {M N : NondegenerateModuleCat.{uR, v} R} (f : M ⟶ N),
    ((restrictedFunctor hS hX hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hX hX (NonUnitalBimoduleHom.id S R X) f.hom := @restrictedFunctor_map_hom

/-! First unequal direction; the actual target carrier universe is max 1 0. -/

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X),
    NonUnitalModuleCat.{1, 0} R ⥤ NonUnitalModuleCat.{0, max 1 0} S := @functor

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X),
    (functor.{0, 1, 1, 0} hX).Additive := @functor_additive

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X)
    (M : Type 0) [AddCommGroup M] [NonUnitalModule R M],
    @IsNondegenerate S (Tensor R X M) _ (NonUnitalModuleTensor.addCommGroup R X M)
      (NonUnitalBimoduleTensor.leftModule hX M) := @isNondegenerate

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    NonUnitalModuleCat.{1, 0} R ⥤ NondegenerateModuleCat.{0, max 1 0} S := @nondegenerateFunctor

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    (nondegenerateFunctor.{0, 1, 1, 0} hS hX hnd).Additive := @nondegenerateFunctor_additive

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    nondegenerateFunctor.{0, 1, 1, 0} hS hX hnd ⋙ nondegenerateInclusion S =
      functor hX := @nondegenerateFunctor_comp_inclusion

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    NondegenerateModuleCat.{1, 0} R ⥤ NondegenerateModuleCat.{0, max 1 0} S := @restrictedFunctor

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    (restrictedFunctor.{0, 1, 1, 0} hS hX hnd).Additive := @restrictedFunctor_additive

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type 0} {N : Type 1} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule R M] [NonUnitalModule R N],
    NonUnitalModuleHom R M N → NonUnitalModuleHom S (tensorObj hX M) (tensorObj hX N) := @map

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type 0} {N : Type 1} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule R M] [NonUnitalModule R N],
    NonUnitalModuleHom R M N →+ NonUnitalModuleHom S (tensorObj hX M) (tensorObj hX N) := @mapAddHom

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type 0} {N : Type 1} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule R M] [NonUnitalModule R N]
    (f : NonUnitalModuleHom R M N),
    (map hX f).toAddMonoidHom =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) f := @map_toAddMonoidHom

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type 0} [AddCommGroup M] [NonUnitalModule R M],
    map hX (NonUnitalModuleHom.id R M) = NonUnitalModuleHom.id S (tensorObj hX M) := @map_id

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type 0} {N : Type 1} {P : Type 0}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [NonUnitalModule R M] [NonUnitalModule R N] [NonUnitalModule R P]
    (g : NonUnitalModuleHom R N P) (f : NonUnitalModuleHom R M N),
    map hX (g.comp f) = (map hX g).comp (map hX f) := @map_comp

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X)
    {M N : NonUnitalModuleCat.{1, 0} R} (f : M ⟶ N),
    ((nondegenerateFunctor hS hX hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hX hX (NonUnitalBimoduleHom.id S R X) f := @nondegenerateFunctor_map_hom

example : ∀ {S : Type 0} {R : Type 1} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 1} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X)
    {M N : NondegenerateModuleCat.{1, 0} R} (f : M ⟶ N),
    ((restrictedFunctor hS hX hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hX hX (NonUnitalBimoduleHom.id S R X) f.hom := @restrictedFunctor_map_hom

/-! Opposite unequal direction; the actual target carrier universe is max 0 1. -/

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X),
    NonUnitalModuleCat.{0, 1} R ⥤ NonUnitalModuleCat.{1, max 0 1} S := @functor

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X),
    (functor.{1, 0, 0, 1} hX).Additive := @functor_additive

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X)
    (M : Type 1) [AddCommGroup M] [NonUnitalModule R M],
    @IsNondegenerate S (Tensor R X M) _ (NonUnitalModuleTensor.addCommGroup R X M)
      (NonUnitalBimoduleTensor.leftModule hX M) := @isNondegenerate

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    NonUnitalModuleCat.{0, 1} R ⥤ NondegenerateModuleCat.{1, max 0 1} S := @nondegenerateFunctor

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    (nondegenerateFunctor.{1, 0, 0, 1} hS hX hnd).Additive := @nondegenerateFunctor_additive

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    nondegenerateFunctor.{1, 0, 0, 1} hS hX hnd ⋙ nondegenerateInclusion S =
      functor hX := @nondegenerateFunctor_comp_inclusion

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    NondegenerateModuleCat.{0, 1} R ⥤ NondegenerateModuleCat.{1, max 0 1} S := @restrictedFunctor

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X),
    (restrictedFunctor.{1, 0, 0, 1} hS hX hnd).Additive := @restrictedFunctor_additive

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type 1} {N : Type 0} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule R M] [NonUnitalModule R N],
    NonUnitalModuleHom R M N → NonUnitalModuleHom S (tensorObj hX M) (tensorObj hX N) := @map

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type 1} {N : Type 0} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule R M] [NonUnitalModule R N],
    NonUnitalModuleHom R M N →+ NonUnitalModuleHom S (tensorObj hX M) (tensorObj hX N) := @mapAddHom

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type 1} {N : Type 0} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule R M] [NonUnitalModule R N]
    (f : NonUnitalModuleHom R M N),
    (map hX f).toAddMonoidHom =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) f := @map_toAddMonoidHom

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type 1} [AddCommGroup M] [NonUnitalModule R M],
    map hX (NonUnitalModuleHom.id R M) = NonUnitalModuleHom.id S (tensorObj hX M) := @map_id

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hX : ActionsCommute S R X)
    {M : Type 1} {N : Type 0} {P : Type 1}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [NonUnitalModule R M] [NonUnitalModule R N] [NonUnitalModule R P]
    (g : NonUnitalModuleHom R N P) (f : NonUnitalModuleHom R M N),
    map hX (g.comp f) = (map hX g).comp (map hX f) := @map_comp

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X)
    {M N : NonUnitalModuleCat.{0, 1} R} (f : M ⟶ N),
    ((nondegenerateFunctor hS hX hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hX hX (NonUnitalBimoduleHom.id S R X) f := @nondegenerateFunctor_map_hom

example : ∀ {S : Type 1} {R : Type 0} [NonUnitalRing S] [NonUnitalRing R]
    {X : Type 0} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
    (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X)
    {M N : NondegenerateModuleCat.{0, 1} R} (f : M ⟶ N),
    ((restrictedFunctor hS hX hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hX hX (NonUnitalBimoduleHom.id S R X) f.hom := @restrictedFunctor_map_hom

end Interfaces

section SourceInterfaces
set_option linter.unusedVariables false

/-! Source specializations with independent ring and variable-carrier universes. -/

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    NondegenerateModuleCat.{uB, v} B ⥤
      NondegenerateModuleCat.{uA, max uB v} A := @F

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    (F.{uA, uB, v} hA hAB hnd).Additive := @F_additive

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    F.{uA, uB, v} hA hAB hnd = restrictedFunctor hA hAB hnd.1 := @F_eq_restrictedFunctor

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    F.{uA, uB, v} hA hAB hnd =
      nondegenerateInclusion B ⋙ nondegenerateFunctor hA hAB hnd.1 := @F_eq_inclusion_comp

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    (M : NondegenerateModuleCat.{uB, v} B),
    ((F.{uA, uB, v} hA hAB hnd).obj M).obj.carrier = Tensor B B M.obj := @F_obj_carrier

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    (M : NondegenerateModuleCat.{uB, v} B),
    ((F.{uA, uB, v} hA hAB hnd).obj M).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup B B M.obj := @F_obj_addCommGroup

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    (M : NondegenerateModuleCat.{uB, v} B),
    ((F.{uA, uB, v} hA hAB hnd).obj M).obj.isModule = NonUnitalBimoduleTensor.leftModule hAB M.obj := @F_obj_module

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N),
    ((F.{uA, uB, v} hA hAB hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hAB hAB (NonUnitalBimoduleHom.id A B B) f.hom := @F_map_hom

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N),
    ((F.{uA, uB, v} hA hAB hnd).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map B (NonUnitalModuleHom.id Bᵐᵒᵖ B) f.hom := @F_map_toAddMonoidHom

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    NondegenerateModuleCat.{uA, v} A ⥤
      NondegenerateModuleCat.{uB, max uB v} B := @P

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    (P.{uA, uB, v} hB hBA hnd).Additive := @P_additive

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    P.{uA, uB, v} hB hBA hnd = restrictedFunctor hB hBA hnd.1 := @P_eq_restrictedFunctor

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    P.{uA, uB, v} hB hBA hnd =
      nondegenerateInclusion A ⋙ nondegenerateFunctor hB hBA hnd.1 := @P_eq_inclusion_comp

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    (M : NondegenerateModuleCat.{uA, v} A),
    ((P.{uA, uB, v} hB hBA hnd).obj M).obj.carrier = Tensor A B M.obj := @P_obj_carrier

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    (M : NondegenerateModuleCat.{uA, v} A),
    ((P.{uA, uB, v} hB hBA hnd).obj M).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup A B M.obj := @P_obj_addCommGroup

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    (M : NondegenerateModuleCat.{uA, v} A),
    ((P.{uA, uB, v} hB hBA hnd).obj M).obj.isModule = NonUnitalBimoduleTensor.leftModule hBA M.obj := @P_obj_module

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N),
    ((P.{uA, uB, v} hB hBA hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hBA hBA (NonUnitalBimoduleHom.id B A B) f.hom := @P_map_hom

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N),
    ((P.{uA, uB, v} hB hBA hnd).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ B) f.hom := @P_map_toAddMonoidHom

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B),
    NondegenerateModuleCat.{uB, v} B ⥤ NondegenerateModuleCat.{uA, max uB v} A := @regularF

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B),
    (regularF.{uA, uB, v} hA hB hAB hLeft).Additive := @regularF_additive

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B),
    regularF.{uA, uB, v} hA hB hAB hLeft =
      @restrictedFunctor A B _ _ B _ _ (NonUnitalModule.rightRegular B) hA hAB hLeft := @regularF_eq_restrictedFunctor

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule Aᵐᵒᵖ B] (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B),
    NondegenerateModuleCat.{uA, v} A ⥤ NondegenerateModuleCat.{uB, max uB v} B := @regularP

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule Aᵐᵒᵖ B] (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B),
    (regularP.{uA, uB, v} hB hBA hRight).Additive := @regularP_additive

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule Aᵐᵒᵖ B] (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B),
    regularP.{uA, uB, v} hB hBA hRight =
      @restrictedFunctor B A _ _ B _ (NonUnitalModule.regular B) _ hB hBA
        (regular_isNondegenerate hB) := @regularP_eq_restrictedFunctor

example : ∀ {B : Type uB} [NonUnitalRing B] (hB : IsIdempotented B),
    @IsNondegenerate B B _ _ (NonUnitalModule.regular B) := @regular_isNondegenerate

example : ∀ {B : Type uB} [NonUnitalRing B] (hB : IsIdempotented B),
    @IsRightNondegenerate B B _ _ (NonUnitalModule.rightRegular B) := @rightRegular_isNondegenerate

example : ∀ {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
    {Y : Type uX} [AddCommGroup Y] [NonUnitalModule A Y] [NonUnitalModule Bᵐᵒᵖ Y]
    (h : IsNondegenerateBimodule A B Y),
    IsNondegenerate A Y := @leftNondegenerate_of_bimodule

/-! Source specializations in the first unequal direction. -/

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    NondegenerateModuleCat.{1, 0} B ⥤
      NondegenerateModuleCat.{0, max 1 0} A := @F

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    (F.{0, 1, 0} hA hAB hnd).Additive := @F_additive

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    F.{0, 1, 0} hA hAB hnd = restrictedFunctor hA hAB hnd.1 := @F_eq_restrictedFunctor

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    F.{0, 1, 0} hA hAB hnd =
      nondegenerateInclusion B ⋙ nondegenerateFunctor hA hAB hnd.1 := @F_eq_inclusion_comp

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    (M : NondegenerateModuleCat.{1, 0} B),
    ((F.{0, 1, 0} hA hAB hnd).obj M).obj.carrier = Tensor B B M.obj := @F_obj_carrier

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    (M : NondegenerateModuleCat.{1, 0} B),
    ((F.{0, 1, 0} hA hAB hnd).obj M).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup B B M.obj := @F_obj_addCommGroup

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    (M : NondegenerateModuleCat.{1, 0} B),
    ((F.{0, 1, 0} hA hAB hnd).obj M).obj.isModule = NonUnitalBimoduleTensor.leftModule hAB M.obj := @F_obj_module

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    {M N : NondegenerateModuleCat.{1, 0} B} (f : M ⟶ N),
    ((F.{0, 1, 0} hA hAB hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hAB hAB (NonUnitalBimoduleHom.id A B B) f.hom := @F_map_hom

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    {M N : NondegenerateModuleCat.{1, 0} B} (f : M ⟶ N),
    ((F.{0, 1, 0} hA hAB hnd).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map B (NonUnitalModuleHom.id Bᵐᵒᵖ B) f.hom := @F_map_toAddMonoidHom

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    NondegenerateModuleCat.{0, 0} A ⥤
      NondegenerateModuleCat.{1, max 1 0} B := @P

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    (P.{0, 1, 0} hB hBA hnd).Additive := @P_additive

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    P.{0, 1, 0} hB hBA hnd = restrictedFunctor hB hBA hnd.1 := @P_eq_restrictedFunctor

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    P.{0, 1, 0} hB hBA hnd =
      nondegenerateInclusion A ⋙ nondegenerateFunctor hB hBA hnd.1 := @P_eq_inclusion_comp

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    (M : NondegenerateModuleCat.{0, 0} A),
    ((P.{0, 1, 0} hB hBA hnd).obj M).obj.carrier = Tensor A B M.obj := @P_obj_carrier

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    (M : NondegenerateModuleCat.{0, 0} A),
    ((P.{0, 1, 0} hB hBA hnd).obj M).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup A B M.obj := @P_obj_addCommGroup

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    (M : NondegenerateModuleCat.{0, 0} A),
    ((P.{0, 1, 0} hB hBA hnd).obj M).obj.isModule = NonUnitalBimoduleTensor.leftModule hBA M.obj := @P_obj_module

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    {M N : NondegenerateModuleCat.{0, 0} A} (f : M ⟶ N),
    ((P.{0, 1, 0} hB hBA hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hBA hBA (NonUnitalBimoduleHom.id B A B) f.hom := @P_map_hom

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    {M N : NondegenerateModuleCat.{0, 0} A} (f : M ⟶ N),
    ((P.{0, 1, 0} hB hBA hnd).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ B) f.hom := @P_map_toAddMonoidHom

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B),
    NondegenerateModuleCat.{1, 0} B ⥤ NondegenerateModuleCat.{0, max 1 0} A := @regularF

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B),
    (regularF.{0, 1, 0} hA hB hAB hLeft).Additive := @regularF_additive

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B),
    regularF.{0, 1, 0} hA hB hAB hLeft =
      @restrictedFunctor A B _ _ B _ _ (NonUnitalModule.rightRegular B) hA hAB hLeft := @regularF_eq_restrictedFunctor

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule Aᵐᵒᵖ B] (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B),
    NondegenerateModuleCat.{0, 0} A ⥤ NondegenerateModuleCat.{1, max 1 0} B := @regularP

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule Aᵐᵒᵖ B] (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B),
    (regularP.{0, 1, 0} hB hBA hRight).Additive := @regularP_additive

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule Aᵐᵒᵖ B] (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B),
    regularP.{0, 1, 0} hB hBA hRight =
      @restrictedFunctor B A _ _ B _ (NonUnitalModule.regular B) _ hB hBA
        (regular_isNondegenerate hB) := @regularP_eq_restrictedFunctor

example : ∀ {B : Type 1} [NonUnitalRing B] (hB : IsIdempotented B),
    @IsNondegenerate B B _ _ (NonUnitalModule.regular B) := @regular_isNondegenerate

example : ∀ {B : Type 1} [NonUnitalRing B] (hB : IsIdempotented B),
    @IsRightNondegenerate B B _ _ (NonUnitalModule.rightRegular B) := @rightRegular_isNondegenerate

example : ∀ {A : Type 0} {B : Type 1} [NonUnitalRing A] [NonUnitalRing B]
    {Y : Type 1} [AddCommGroup Y] [NonUnitalModule A Y] [NonUnitalModule Bᵐᵒᵖ Y]
    (h : IsNondegenerateBimodule A B Y),
    IsNondegenerate A Y := @leftNondegenerate_of_bimodule

/-! Source specializations in the opposite unequal direction. -/

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    NondegenerateModuleCat.{0, 1} B ⥤
      NondegenerateModuleCat.{1, max 0 1} A := @F

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    (F.{1, 0, 1} hA hAB hnd).Additive := @F_additive

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    F.{1, 0, 1} hA hAB hnd = restrictedFunctor hA hAB hnd.1 := @F_eq_restrictedFunctor

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B),
    F.{1, 0, 1} hA hAB hnd =
      nondegenerateInclusion B ⋙ nondegenerateFunctor hA hAB hnd.1 := @F_eq_inclusion_comp

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    (M : NondegenerateModuleCat.{0, 1} B),
    ((F.{1, 0, 1} hA hAB hnd).obj M).obj.carrier = Tensor B B M.obj := @F_obj_carrier

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    (M : NondegenerateModuleCat.{0, 1} B),
    ((F.{1, 0, 1} hA hAB hnd).obj M).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup B B M.obj := @F_obj_addCommGroup

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    (M : NondegenerateModuleCat.{0, 1} B),
    ((F.{1, 0, 1} hA hAB hnd).obj M).obj.isModule = NonUnitalBimoduleTensor.leftModule hAB M.obj := @F_obj_module

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    {M N : NondegenerateModuleCat.{0, 1} B} (f : M ⟶ N),
    ((F.{1, 0, 1} hA hAB hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hAB hAB (NonUnitalBimoduleHom.id A B B) f.hom := @F_map_hom

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
    (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
    (hnd : IsNondegenerateBimodule A B B)
    {M N : NondegenerateModuleCat.{0, 1} B} (f : M ⟶ N),
    ((F.{1, 0, 1} hA hAB hnd).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map B (NonUnitalModuleHom.id Bᵐᵒᵖ B) f.hom := @F_map_toAddMonoidHom

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    NondegenerateModuleCat.{1, 1} A ⥤
      NondegenerateModuleCat.{0, max 0 1} B := @P

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    (P.{1, 0, 1} hB hBA hnd).Additive := @P_additive

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    P.{1, 0, 1} hB hBA hnd = restrictedFunctor hB hBA hnd.1 := @P_eq_restrictedFunctor

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B),
    P.{1, 0, 1} hB hBA hnd =
      nondegenerateInclusion A ⋙ nondegenerateFunctor hB hBA hnd.1 := @P_eq_inclusion_comp

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    (M : NondegenerateModuleCat.{1, 1} A),
    ((P.{1, 0, 1} hB hBA hnd).obj M).obj.carrier = Tensor A B M.obj := @P_obj_carrier

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    (M : NondegenerateModuleCat.{1, 1} A),
    ((P.{1, 0, 1} hB hBA hnd).obj M).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup A B M.obj := @P_obj_addCommGroup

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    (M : NondegenerateModuleCat.{1, 1} A),
    ((P.{1, 0, 1} hB hBA hnd).obj M).obj.isModule = NonUnitalBimoduleTensor.leftModule hBA M.obj := @P_obj_module

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    {M N : NondegenerateModuleCat.{1, 1} A} (f : M ⟶ N),
    ((P.{1, 0, 1} hB hBA hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hBA hBA (NonUnitalBimoduleHom.id B A B) f.hom := @P_map_hom

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
    (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
    (hnd : IsNondegenerateBimodule B A B)
    {M N : NondegenerateModuleCat.{1, 1} A} (f : M ⟶ N),
    ((P.{1, 0, 1} hB hBA hnd).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ B) f.hom := @P_map_toAddMonoidHom

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B),
    NondegenerateModuleCat.{0, 1} B ⥤ NondegenerateModuleCat.{1, max 0 1} A := @regularF

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B),
    (regularF.{1, 0, 1} hA hB hAB hLeft).Additive := @regularF_additive

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule A B] (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B),
    regularF.{1, 0, 1} hA hB hAB hLeft =
      @restrictedFunctor A B _ _ B _ _ (NonUnitalModule.rightRegular B) hA hAB hLeft := @regularF_eq_restrictedFunctor

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule Aᵐᵒᵖ B] (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B),
    NondegenerateModuleCat.{1, 1} A ⥤ NondegenerateModuleCat.{0, max 0 1} B := @regularP

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule Aᵐᵒᵖ B] (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B),
    (regularP.{1, 0, 1} hB hBA hRight).Additive := @regularP_additive

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    [NonUnitalModule Aᵐᵒᵖ B] (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B),
    regularP.{1, 0, 1} hB hBA hRight =
      @restrictedFunctor B A _ _ B _ (NonUnitalModule.regular B) _ hB hBA
        (regular_isNondegenerate hB) := @regularP_eq_restrictedFunctor

example : ∀ {B : Type 0} [NonUnitalRing B] (hB : IsIdempotented B),
    @IsNondegenerate B B _ _ (NonUnitalModule.regular B) := @regular_isNondegenerate

example : ∀ {B : Type 0} [NonUnitalRing B] (hB : IsIdempotented B),
    @IsRightNondegenerate B B _ _ (NonUnitalModule.rightRegular B) := @rightRegular_isNondegenerate

example : ∀ {A : Type 1} {B : Type 0} [NonUnitalRing A] [NonUnitalRing B]
    {Y : Type 0} [AddCommGroup Y] [NonUnitalModule A Y] [NonUnitalModule Bᵐᵒᵖ Y]
    (h : IsNondegenerateBimodule A B Y),
    IsNondegenerate A Y := @leftNondegenerate_of_bimodule

end SourceInterfaces

/-! Explicit structure selection while unrelated instances coexist. -/

section CompetingStructures
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable (S : Type uS) (R : Type uR) (X : Type uX) (M : Type v)
  (s₀ : NonUnitalRing S) [s₁ : NonUnitalRing S]
  (r₀ : NonUnitalRing R) [r₁ : NonUnitalRing R]
  (gx₀ : AddCommGroup X) [gx₁ : AddCommGroup X]
  (gm₀ : AddCommGroup M) [gm₁ : AddCommGroup M]
  (xS₀ : @NonUnitalModule S X s₀ gx₀)
  (xR₀ : letI := r₀; @NonUnitalModule Rᵐᵒᵖ X _ gx₀)
  (mR₀ : @NonUnitalModule R M r₀ gm₀)
  (hX : @ActionsCommute S R X s₀ r₀ gx₀ xS₀ xR₀)
  [xS₁ : @NonUnitalModule S X s₁ gx₁]
  [xR₁ : letI := r₁; @NonUnitalModule Rᵐᵒᵖ X _ gx₁]
  [mR₁ : @NonUnitalModule R M r₁ gm₁]

local notation "Q" => @Tensor R X M r₀ gx₀ gm₀ xR₀ mR₀
local notation "GQ" => @NonUnitalModuleTensor.addCommGroup R X M r₀ gx₀ gm₀ xR₀ mR₀
local notation "LQ" => @NonUnitalBimoduleTensor.leftModule S R s₀ r₀ X gx₀ xS₀ xR₀ hX M gm₀ mR₀
local notation "M₀" => @NonUnitalModuleCat.of R r₀ M gm₀ mR₀
local notation "F₀" => @functor S R s₀ r₀ X gx₀ xS₀ xR₀ hX

variable [gq₁ : AddCommGroup (@Tensor R X M r₀ gx₀ gm₀ xR₀ mR₀)]
  [qS₁ : @NonUnitalModule S (@Tensor R X M r₀ gx₀ gm₀ xR₀ mR₀) s₁ gq₁]

include s₁ r₁ gx₁ gm₁ xS₁ xR₁ mR₁ gq₁ qS₁

example : (inferInstance : NonUnitalRing S) = s₁ := rfl
example : (inferInstance : NonUnitalRing R) = r₁ := rfl
example : (inferInstance : AddCommGroup X) = gx₁ := rfl
example : (inferInstance : AddCommGroup M) = gm₁ := rfl
example : (inferInstance : NonUnitalModule S X) = xS₁ := rfl
example : (inferInstance : NonUnitalModule Rᵐᵒᵖ X) = xR₁ := rfl
example : (inferInstance : NonUnitalModule R M) = mR₁ := rfl
example : (inferInstance : AddCommGroup Q) = gq₁ := rfl
example : (inferInstance : @NonUnitalModule S Q s₁ gq₁) = qS₁ := rfl

example : @NonUnitalModuleCat.carrier S s₀ ((F₀).obj M₀) = Q := rfl
example : @NonUnitalModuleCat.isAddCommGroup S s₀ ((F₀).obj M₀) = GQ := rfl
example : @NonUnitalModuleCat.isModule S s₀ ((F₀).obj M₀) = LQ := rfl

example (f : @NonUnitalModuleHom R M M r₀ gm₀ gm₀ mR₀ mR₀) :
    @NonUnitalModuleHom.toAddMonoidHom S Q Q s₀ GQ GQ LQ LQ
      ((F₀).map (X := M₀) (Y := M₀) f) =
      @NonUnitalModuleTensor.map R X M r₀ gx₀ gm₀ xR₀ mR₀ X M gx₀ gm₀ xR₀ mR₀
        (@NonUnitalModuleHom.id Rᵐᵒᵖ X (by letI := r₀; infer_instance) gx₀ xR₀) f := rfl

example (f : @NonUnitalModuleHom R M M r₀ gm₀ gm₀ mR₀ mR₀) :
    (F₀).map (X := M₀) (Y := M₀) f =
      @NonUnitalBimoduleTensor.leftMap S R s₀ r₀ X gx₀ xS₀ xR₀ X gx₀ xS₀ xR₀
        M gm₀ mR₀ M gm₀ mR₀ hX hX
        (@NonUnitalBimoduleHom.id S R X s₀ r₀ gx₀ xS₀ xR₀) f := rfl

variable (hS : @IsIdempotented S s₀) (hnd : @IsNondegenerate S X s₀ gx₀ xS₀)

local notation "ND₀" => @nondegenerateFunctor
  S R s₀ r₀ X gx₀ xS₀ xR₀ hS hX hnd

example : @IsNondegenerate S Q s₀ GQ LQ :=
  @isNondegenerate S R s₀ r₀ X gx₀ xS₀ xR₀ hS hX hnd M gm₀ mR₀

example : @NonUnitalModuleCat.carrier S s₀ ((ND₀).obj M₀).obj = Q := rfl
example : @NonUnitalModuleCat.isAddCommGroup S s₀ ((ND₀).obj M₀).obj = GQ := rfl
example : @NonUnitalModuleCat.isModule S s₀ ((ND₀).obj M₀).obj = LQ := rfl

example (f : @NonUnitalModuleHom R M M r₀ gm₀ gm₀ mR₀ mR₀) :
    ((ND₀).map (X := M₀) (Y := M₀) f).hom = (F₀).map (X := M₀) (Y := M₀) f := rfl

end CompetingStructures

/-! Named source regular actions remain selected in the presence of alternatives. -/

section SourceStructureSelection
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]

section F
variable [NonUnitalModule A B] [otherRight : NonUnitalModule Bᵐᵒᵖ B]
  (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
  (hLeft : IsNondegenerate A B)

include otherRight
example : (inferInstance : NonUnitalModule Bᵐᵒᵖ B) = otherRight := rfl

example (M : NondegenerateModuleCat.{uB, v} B) :
    ((regularF hA hB hAB hLeft).obj M).obj.carrier =
      @Tensor B B M.obj _ _ _ (NonUnitalModule.rightRegular B) _ := rfl

example (M : NondegenerateModuleCat.{uB, v} B) :
    ((regularF hA hB hAB hLeft).obj M).obj.isAddCommGroup =
      @NonUnitalModuleTensor.addCommGroup B B M.obj _ _ _ (NonUnitalModule.rightRegular B) _ := rfl

example (M : NondegenerateModuleCat.{uB, v} B) :
    ((regularF hA hB hAB hLeft).obj M).obj.isModule =
      @NonUnitalBimoduleTensor.leftModule A B _ _ B _ _ (NonUnitalModule.rightRegular B)
        hAB M.obj _ _ := rfl

example {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N) :
    ((regularF hA hB hAB hLeft).map f).hom.toAddMonoidHom =
      @NonUnitalModuleTensor.map B B M.obj _ _ _ (NonUnitalModule.rightRegular B) _
        B N.obj _ _ (NonUnitalModule.rightRegular B) _
        (@NonUnitalModuleHom.id Bᵐᵒᵖ B _ _ (NonUnitalModule.rightRegular B)) f.hom := rfl

end F

section P
variable [NonUnitalModule Aᵐᵒᵖ B] [otherLeft : NonUnitalModule B B]
  (hB : IsIdempotented B)
  (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
  (hRight : IsRightNondegenerate A B)

include otherLeft
example : (inferInstance : NonUnitalModule B B) = otherLeft := rfl

example (M : NondegenerateModuleCat.{uA, v} A) :
    ((regularP hB hBA hRight).obj M).obj.isModule =
      @NonUnitalBimoduleTensor.leftModule B A _ _ B _ (NonUnitalModule.regular B) _
        hBA M.obj _ _ := rfl

example (M : NondegenerateModuleCat.{uA, v} A) :
    ((regularP hB hBA hRight).obj M).obj.carrier = Tensor A B M.obj := rfl

example {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N) :
    ((regularP hB hBA hRight).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ B) f.hom := rfl

end P
end SourceStructureSelection

/-! Subsingleton and zero-ring boundary cases retain arbitrary universes. -/

section SubsingletonCases
variable {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
  {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  (hS : IsIdempotented S) (hX : ActionsCommute S R X)
  (M : Type v) [AddCommGroup M] [NonUnitalModule R M]

example [Subsingleton X] :
    @IsNondegenerate S (Tensor R X M) _ (NonUnitalModuleTensor.addCommGroup R X M)
      (NonUnitalBimoduleTensor.leftModule hX M) :=
  isNondegenerate hS hX (isNondegenerateBimodule_of_subsingleton (A := S) (B := R)).1 M

example [Subsingleton X] : NondegenerateModuleCat.{uS, max uX v} S :=
  (nondegenerateFunctor hS hX
    (isNondegenerateBimodule_of_subsingleton (A := S) (B := R)).1).obj
      (NonUnitalModuleCat.of R M)

example [Subsingleton X] : Subsingleton (tensorObj hX M) := by
  have h : AddMonoidHom.id (tensorObj hX M) = 0 :=
    NonUnitalModuleTensor.hom_ext R fun x m => by
      change tmul R X M x m = 0
      rw [Subsingleton.elim x 0, NonUnitalModuleTensor.zero_tmul]
  exact ⟨fun a b => (DFunLike.congr_fun h a).trans (DFunLike.congr_fun h b).symm⟩

/-- Even with an arbitrary first factor, a trivial second factor gives a trivial output. -/
example [Subsingleton M] :
    @IsNondegenerate S (Tensor R X M) _ (NonUnitalModuleTensor.addCommGroup R X M)
      (NonUnitalBimoduleTensor.leftModule hX M) := by
  have h : AddMonoidHom.id (tensorObj hX M) = 0 :=
    NonUnitalModuleTensor.hom_ext R fun x m => by
      change tmul R X M x m = 0
      rw [Subsingleton.elim m 0, NonUnitalModuleTensor.tmul_zero]
  let := NonUnitalBimoduleTensor.leftModule hX M
  intro t
  refine ⟨⟨0, IsIdempotentElem.zero⟩, ?_⟩
  exact (NonUnitalModule.zero_smul t).trans (DFunLike.congr_fun h t).symm

/-- Zero rings in unrelated universes allow the ambient functor on nonzero carriers. -/
example : NonUnitalModuleCat.{uR, v} PUnit.{uR + 1} ⥤
    NonUnitalModuleCat.{uS, max 0 v} PUnit.{uS + 1} :=
  @functor PUnit PUnit _ _ ℤ _ NonUnitalModule.zero NonUnitalModule.zero
    (@actionsCommute_zero_left PUnit PUnit ℤ _ _ _ NonUnitalModule.zero)

end SubsingletonCases

private def integerPairing : ℤ →+ ℤ →+ ℤ where
  toFun x :=
    { toFun m := x * m
      map_zero' := mul_zero x
      map_add' := mul_add x }
  map_zero' := AddMonoidHom.ext zero_mul
  map_add' x x' := AddMonoidHom.ext (fun m => add_mul x x' m)

/-! The unital ring of integers may act by zero on a nonzero ambient tensor. -/

section ZeroIntegerActions
local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.zero
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.zero

private theorem zeroCommute : ActionsCommute ℤ ℤ ℤ := actionsCommute_zero_left
private abbrev zeroFunctor := functor.{0, 0, 0, 0} zeroCommute
private abbrev zeroObject := zeroFunctor.obj (NonUnitalModuleCat.of ℤ ℤ)

private theorem zeroPairing_balanced : NonUnitalModuleTensor.IsBalanced ℤ integerPairing := by
  intro a x m
  change (0 : ℤ) * m = x * 0
  rw [zero_mul, mul_zero]

private theorem zeroTensor_one_ne_zero : tmul ℤ ℤ ℤ 1 1 ≠ 0 := by
  intro h
  have h' := congrArg (NonUnitalModuleTensor.lift ℤ integerPairing zeroPairing_balanced) h
  change (1 : ℤ) = 0 at h'
  exact one_ne_zero h'

example : Nontrivial zeroObject :=
  ⟨⟨tmul ℤ ℤ ℤ 1 1, 0, zeroTensor_one_ne_zero⟩⟩

example (s : ℤ) : NonUnitalModule.toEndHom zeroObject.isModule s = 0 := by
  apply NonUnitalModuleTensor.hom_ext ℤ
  intro x m
  change tmul ℤ ℤ ℤ 0 m = 0
  exact NonUnitalModuleTensor.zero_tmul _ _ _ _

example : ¬ @IsUnitalModule ℤ zeroObject _ zeroObject.isAddCommGroup zeroObject.isModule := by
  intro h
  have h' := h (tmul ℤ ℤ ℤ 1 1)
  change tmul ℤ ℤ ℤ 0 1 = tmul ℤ ℤ ℤ 1 1 at h'
  rw [NonUnitalModuleTensor.zero_tmul] at h'
  exact zeroTensor_one_ne_zero h'.symm

example : ¬ IsNondegenerate ℤ zeroObject := by
  intro h
  obtain ⟨e, he⟩ := h (tmul ℤ ℤ ℤ 1 1)
  change tmul ℤ ℤ ℤ 0 1 = tmul ℤ ℤ ℤ 1 1 at he
  rw [NonUnitalModuleTensor.zero_tmul] at he
  exact zeroTensor_one_ne_zero he.symm

end ZeroIntegerActions

/-! The intrinsic law admits degenerate balancing actions on both factors. -/

section DegenerateSecondFactor
local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.zero
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.zero

/-- A regular left integer action and the zero right integer action on the first factor. -/
private abbrev mixedBimodule : NonUnitalBimoduleCat.{0, 0, 0} ℤ ℤ :=
  @NonUnitalBimoduleCat.of ℤ ℤ _ _ ℤ _ (NonUnitalModule.regular ℤ) NonUnitalModule.zero
    (@actionsCommute_zero_right ℤ ℤ ℤ _ _ _ (NonUnitalModule.regular ℤ))

private abbrev degenerateSecond : NonUnitalModuleCat.{0, 0} ℤ :=
  @NonUnitalModuleCat.of ℤ _ ℤ _ NonUnitalModule.zero

private abbrev mixedFunctor : NonUnitalModuleCat.{0, 0} ℤ ⥤ NondegenerateModuleCat.{0, 0} ℤ :=
  @nondegenerateFunctor ℤ ℤ _ _ ℤ _ (NonUnitalModule.regular ℤ) NonUnitalModule.zero
    (IsIdempotented.of_ring ℤ) mixedBimodule.actionsCommute
    (regular_isNondegenerate (IsIdempotented.of_ring ℤ))

private abbrev mixedObject := (mixedFunctor.obj degenerateSecond).obj

example : ¬ IsNondegenerate ℤ degenerateSecond := by
  intro h
  obtain ⟨e, he⟩ := h 1
  change (0 : ℤ) = 1 at he
  exact zero_ne_one he

example : ¬ @IsRightNondegenerate ℤ mixedBimodule _ mixedBimodule.isAddCommGroup
    mixedBimodule.isRightModule := by
  intro h
  obtain ⟨e, he⟩ := h 1
  change (0 : ℤ) = 1 at he
  exact zero_ne_one he

example : IsNondegenerate ℤ mixedObject := (mixedFunctor.obj degenerateSecond).property

private theorem mixedPairing_balanced :
    NonUnitalModuleTensor.IsBalanced ℤ (X := mixedBimodule) (Y := degenerateSecond) integerPairing := by
  intro a x m
  change (0 : ℤ) * m = x * 0
  rw [zero_mul, mul_zero]

private theorem mixedTensor_one_ne_zero :
    tmul ℤ mixedBimodule degenerateSecond 1 1 ≠ 0 := by
  intro h
  have h' := congrArg (NonUnitalModuleTensor.lift ℤ integerPairing mixedPairing_balanced) h
  change (1 : ℤ) = 0 at h'
  exact one_ne_zero h'

example : Nontrivial mixedObject :=
  ⟨⟨tmul ℤ mixedBimodule degenerateSecond 1 1, 0, mixedTensor_one_ne_zero⟩⟩

example : (2 : ℤ) • (tmul ℤ mixedBimodule degenerateSecond 1 1 : mixedObject) =
    tmul ℤ mixedBimodule degenerateSecond 2 1 := rfl

example : (1 : ℤ) • (tmul ℤ mixedBimodule degenerateSecond 1 1 : mixedObject) =
    tmul ℤ mixedBimodule degenerateSecond 1 1 := rfl

end DegenerateSecondFactor

/-! Regular integer actions give an actual nondegenerate tensor object and map. -/

section RegularIntegerActions
local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ
private abbrev integerRegular := NonUnitalBimoduleCat.regular ℤ
private abbrev integerModule := @NonUnitalModuleCat.of ℤ _ ℤ _ (NonUnitalModule.regular ℤ)
private abbrev regularTensorFunctor :=
  nondegenerateFunctor.{0, 0, 0, 0} (IsIdempotented.of_ring ℤ) integerRegular.actionsCommute
    (regular_isNondegenerate (IsIdempotented.of_ring ℤ))
private abbrev regularTensorObject := (regularTensorFunctor.obj integerModule).obj

example : IsNondegenerate ℤ regularTensorObject := (regularTensorFunctor.obj integerModule).property

example : (2 : ℤ) • (tmul ℤ integerRegular integerModule 1 1 : regularTensorObject) =
    tmul ℤ integerRegular integerModule 2 1 := rfl

example : ((regularTensorFunctor.map (NonUnitalModuleHom.id ℤ integerModule)).hom.toAddMonoidHom)
    (tmul ℤ integerRegular integerModule 1 1) = tmul ℤ integerRegular integerModule 1 1 := rfl

private theorem regularPairing_balanced : NonUnitalModuleTensor.IsBalanced ℤ
    (X := integerRegular) (Y := integerModule) integerPairing := by
  intro a x m
  change (x * a) * m = x * (a * m)
  exact mul_assoc x a m

example : (tmul ℤ integerRegular integerModule 1 1 : regularTensorObject) ≠ 0 := by
  intro h
  have h' := congrArg (NonUnitalModuleTensor.lift ℤ integerPairing regularPairing_balanced) h
  change (1 : ℤ) = 0 at h'
  exact one_ne_zero h'

end RegularIntegerActions

end Langlands.Algebra.NondegenerateTensorFunctorChecks
