# The monoidal and explicit sheafified tensor products

For two module sheaves `A` and `B` over a scheme, `monoidalTensorIso A B` identifies the FLT monoidal tensor with the explicit sheafified tensor `Langlands.Scheme.Modules.tensorObj A B`. It is the inverse of `Scheme.Modules.tensorIsoSheafify A B`. The tensor-power and Picard constructions use this comparison at the same FLT monoidal instance.
